namespace Railways

open Railways.Types

module Preprocess =

    let valueSet m =
        Map.fold (fun s _ v -> Set.add v s) Set.empty m

    let keySet m =
        Map.fold (fun s k _ -> Set.add k s) Set.empty m

    // Used for creating the railway graph
    let addVertex ((l1,l2):Rail) (m:RailwayGraph) = 
        let ll = Map.find l1 m
        Map.add l1 (l2::ll) m


    // Distance from Location l in direction d to all other reachable locations
    // TODO : Make smart by use of already calculated distances
    // Find all end points left or right
    // Calculate their distances to all reachable locations
    // Then for each next location use the distance already calculated
    let rec CreateDistanceMapLoc (loc:Location) (currentLocations:Set<Location>) (explored:Set<Location>) c m rwg =
        match Set.isEmpty currentLocations with
        | true -> m
        | _ -> let nexts = Set.difference (Set.fold (fun s v -> Set.ofList (Map.find v rwg) + s) Set.empty currentLocations) explored
               let nm = Set.fold (fun s v -> Map.add (loc,v) c (Map.add (v,loc) c s)) m nexts
               CreateDistanceMapLoc loc nexts (Set.union nexts explored) (c+1) nm rwg


    let CreateDistanceMap ll rwg = List.fold (fun m v -> CreateDistanceMapLoc v (set [v]) (set [v]) 1 (Map.add (v,v) 0 m) rwg) Map.empty ll


    // Found by taking intersection of reachable locations going train direction from starting location and the opposite direction from the goal location
    let FindPaths (tl:(Train*Location) list) trains left right goal =
        let rec Path d s =
            let rwg = match d with
                      | L -> left
                      | _ -> right
            let x = Set.fold (fun st v -> Set.union (Set.ofList (Map.find v rwg)) st) s s
            match x = s with
            | true -> x
            | _ -> Path d x

        List.fold (fun s (t,d) -> let sl = snd (List.find (fun (x,_) -> x = t) tl)
                                  let gl = Map.find t goal
                                  let paths1 = Path d (set [sl])
                                  let a = if d = L then R else L
                                  let paths2 = Path a (set [gl])
                                  let paths = Set.intersect paths1 paths2
                                  Map.add t paths s) Map.empty trains


    //Finds all distinct paths for the trains, and saves them individually
    let FindDistinctPaths tm gm tdl rwgl rwgr = 
        let rec DistinctPath (rwg:RailwayGraph) (sll:Set<Location list>) =
            match Set.forall (fun v -> List.isEmpty (Map.find (List.head v) rwg)) sll with
            | true -> sll
            | false -> let nsll = Set.fold (fun s v -> let ll = Map.find (List.head v) rwg
                                                       match ll with
                                                       | []  -> Set.add v s
                                                       | [x] -> Set.add (x::v) s
                                                       | [x;y] -> Set.add (x::v) (Set.add (y::v) s)
                                                       | _ -> failwith "Location has more than two options, should not be possible") Set.empty sll


                       DistinctPath rwg nsll
        let rec RemovePath l ll = 
            match ll with
            | [] -> Set.empty
            | x::xs when x = l -> Set.ofList ll
            | x::xs -> RemovePath l xs
        List.fold (fun s (t,d) -> let rwg = if d = R then rwgr else rwgl
                                  let l = Map.find t tm
                                  let g = Map.find t gm
                                  let sll = set [[l]]
                                  let sll = DistinctPath rwg sll
                                  let nSll = Set.fold (fun sx vx -> let p = RemovePath g vx
                                                                    if Set.isEmpty p then sx else Set.add p sx) Set.empty sll
                                  Map.add t nSll s) Map.empty tdl
            

    // Calculates priorities for trains in swap non-cycles
    let rec CalculatePriorities (pre:Map<Train,int>) (cur:Map<Train,int>) (tm:TrainMap) (gm:Map<Location,Train>) x =
        match pre = cur with
        | true -> cur
        | false -> let maxPrio = Map.count tm + x
                   let nm = Map.fold (fun s t l -> if Map.containsKey l gm && Map.containsKey t cur then Map.add t (min (Map.find (Map.find l gm) cur + 1) maxPrio) s else s) cur tm 
                   CalculatePriorities cur nm tm gm x


    // Find the trains that needs to swap locations
    let Swappers tm gm =
        Map.fold (fun s k v -> if Map.containsKey v gm then Set.add k (Set.add (Map.find v gm) s) else s) Set.empty tm

    // Calculates if a given train is part of a swap cycle, and if so return the swap cycle
    let rec SwapCycle (tm:TrainMap) gm t s =
        let l = Map.find t tm 
        match Map.tryFind l gm with
        | Some(tr) -> match Set.contains tr s with
                      | true -> Set.add t s
                      | false -> SwapCycle tm gm tr (Set.add t s)
        | None -> Set.empty 

    // Finds all swap cycles in the network
    let rec FindSwapCycles (tm:TrainMap) gm =
        Map.fold (fun s t l -> let cycle = (SwapCycle tm gm t Set.empty) 
                               if Set.isEmpty cycle then s else Set.add cycle s) Set.empty tm

    // Calculates the distance * path value used to give priorities to trains
    let PathDistance (g:Location) (ps:Set<Location>) (dm:DistanceMap) = 
        Set.fold (fun s v -> s + Map.find (v,g) dm) 0 ps

    // Calculates the priority of all swap cycles in the network
    let PrioritiesSwapCycle (ts:Set<Set<Train>>) (gm:TrainMap) (paths:Map<Train,Set<Location>>) (ds:Map<Train,Direction>) (dm:DistanceMap) =
        Set.fold (fun (sm,sc) v -> let l = Set.fold (fun sx t -> (PathDistance (Map.find t gm) (Map.find t paths) dm,t)::sx) [] v
                                   let sl = List.sortDescending l
                                   let ll,_ = List.fold (fun (sl,c) (_,t) -> Map.add t (c+sc) sl,(c+1)) (sm,1) sl
                                   (ll,sc+(Map.count gm))) (Map.empty,0) ts
                                   
    // Function to give priority to trains that have a free path to goal, and give trains that have non crossing path same priority
    let rec PriorityFun (curLoc:Map<Train,Location>) (ts:Set<Train>) (gs:Map<Train,Location>) (paths:Map<Train,Set<Set<Location>>>) (pm:Map<Train,int>) (c:int) (swaps:Set<Train>) =
        match Set.isEmpty ts with
        | true  -> pm,paths
        | false -> // Find all trains the have an open path from start to goal, in current setup, and does not block trains by being in goal location
                   let freeTrain = Set.fold (fun s t -> let pathSet = Map.find t paths
                                                        //Location of the other trains
                                                        let locs = (Set.remove (Map.find t curLoc) (valueSet curLoc))
                                                        //Checks if given train has a path that does not intersect with location of other trains
                                                        match Set.exists (fun path -> Set.isEmpty (Set.intersect locs path)) pathSet with
                                                        | true -> //Checks if putting train in goal blocks other from being able to get to goal
                                                                  let g = Map.find t gs
                                                                  let allPaths = Set.fold (fun s v -> let ps = Map.find v paths
                                                                                                      let p = Set.fold (fun sx vx -> sx+vx) Set.empty ps
                                                                                                      if v <> t then p+s else s) Set.empty (ts+swaps)
                                                                  match Set.contains g allPaths with
                                                                  | false -> Set.add t s
                                                                  | _ -> s
                                                        | _ -> s) Set.empty ts
                   match Set.isEmpty freeTrain with
                   | true  -> pm,paths
                   | false -> //Finds lists of trains with open path, that have non crossing paths
                              let t = Set.fold (fun s v -> let pathSet = Map.find v paths

                                                           let locs = (Set.remove (Map.find v curLoc) (valueSet curLoc))
                                                           let p = Set.fold (fun sx vx -> if Set.isEmpty (Set.intersect locs vx) && (Set.count vx < Set.count sx || Set.isEmpty sx) then vx else sx) Set.empty pathSet
                                                           let (x,_) = Set.fold (fun (sx,xx) vx -> let px = Map.find vx paths
                                                                                                   let py = Set.fold (fun sz vz -> if Set.isEmpty (Set.intersect vz xx) && (Set.count vz < Set.count sz || Set.isEmpty sz) then vz else sz) Set.empty px
                                                                                                   if Set.isEmpty py 
                                                                                                   then (sx,xx)
                                                                                                   else vx::sx,xx+py) ([v],p) freeTrain

                                                           Set.add x s) Set.empty freeTrain
                              //Pick the list with the most trains
                              let bts = Set.fold (fun s v -> if List.length v > List.length s then v else s) [] t
                              //Update the path of the trains to the ones not crossing
                              let paths,_ = List.fold (fun (s,sp) v -> let locs = (Set.remove (Map.find v curLoc) (valueSet curLoc)) + sp
                                                                       let pathSet = Map.find v paths
                                                                       let p = Set.fold (fun sx vx -> if Set.isEmpty (Set.intersect locs vx) && (Set.count vx < Set.count sx || Set.isEmpty sx) then vx else sx) Set.empty pathSet
                                                                       (Map.add v (set [p]) s),sp+p) (paths,Set.empty) (List.rev bts)                           
                              //Update location of trains, as if the just pciked trains have been move to their goal locations
                              let curLoc = List.fold (fun s v -> Map.add v (Map.find v gs) s) curLoc bts
                              //Remove the trains from the set of trains not in goal
                              let ts = List.fold (fun s v -> Set.remove v s) ts bts
                              //Give the trains a priority
                              let pm = List.fold (fun s v -> Map.add v c s) pm bts
                              let c = c - 1

                              PriorityFun curLoc ts gs paths pm c swaps
                              

    let PathIsUsable (t:Train) (ls:Set<Location>) (paths:Map<Train,Set<Set<Location>>>) = 
        let ps = Map.find t paths
        Set.exists (fun v -> not (Set.isSubset v ls)) ps

    let rec SwapperPaths priomap swappers paths =
        if Map.count priomap <> 0
        then 
            let maxP = Map.fold (fun s k v -> max s v) 0 priomap
            let t = Map.findKey (fun k v -> v = maxP && Set.contains k swappers) priomap
            let swaps = Set.remove t swappers
            let ps = Map.find t paths
            match Set.count ps with
            | 1 -> SwapperPaths (Map.remove t priomap) (swappers) (Map.add t (Set.minElement (set[ps])) paths)
            | _ -> let gp = Set.fold (fun s v -> match Set.forall (fun t -> PathIsUsable t v paths) swaps with
                                                 | true -> Set.add v s
                                                 | _ -> s
                                     ) Set.empty ps
                   match Set.count gp with
                   | 0 -> failwith "Appearantly train has no usable paths oops"
                   | 1 -> SwapperPaths (Map.remove t priomap) (swappers) (Map.add t gp paths)
                   | _ -> let bp = Set.fold (fun s v -> if Set.count v < Set.count s then v else s) (Set.maxElement gp) gp
                          SwapperPaths (Map.remove t priomap) (swappers) (Map.add t (set[bp]) paths)
        else 
            Map.fold (fun s k v -> Map.add k (Set.unionMany (Set.toSeq v)) s) Map.empty paths





    // InitiateState creates the initial state given a railway network, and static global variables
    let InitiateState (ll,rl,srl,sl,tl) = 


        // Create the initial signal, train and switchrail maps
        let sm = List.fold (fun s v -> Map.add v false s) Map.empty sl
        let tm = List.fold (fun s (t,l,_,_) -> Map.add t l s) Map.empty tl
        let rm = List.fold (fun s (l1,l2,l3,d) -> (Map.add (l1,l2,l3,d) true) s) Map.empty srl

        // List of Train * Direction and map of train and the goal location
        let trains,goal = (List.fold (fun (st,sg) (t,_,l,d) -> (t,d)::st,Map.add t l sg) ([],Map.empty) tl)


        // Create a map to get the switch rail from a rail
        let addAllSwitchrail (x:SwitchRail) m =
            let (l1,l2,l3,d) = x
            Map.add (l1,l2) x (Map.add (l2,l1) x (Map.add (l1,l3) x (Map.add (l3,l1) x m)))

        let sr = List.fold (fun s v -> addAllSwitchrail v s) Map.empty srl


        // Create the railway graph going left and right
        let rwg = List.fold (fun s l -> Map.add l [] s) Map.empty ll
        let rwgL = List.fold (fun s (l1,l2) -> addVertex (max l1 l2,min l1 l2) s) rwg rl
        let rwgLeft = List.fold (fun s (l1,l2,l3,d) -> if d = L then addVertex (l1,l2) (addVertex (l1,l3) s) else addVertex (l2,l1) (addVertex (l3,l1) s)) rwgL srl
        let rwgRight = Map.fold (fun s l ll -> List.fold (fun ss loc -> Map.add loc (l::Map.find loc ss) ss) s ll) rwg rwgLeft

        // Create the distance map
        let distanceMap = CreateDistanceMap ll rwgLeft

        // Find all distinct paths from start to end location for all trains
        let paths = FindPaths (Map.toList tm) trains rwgLeft rwgRight goal
        let distinctPaths = FindDistinctPaths tm goal trains rwgLeft rwgRight
        //UNCOMMENT TO CHECK DIFFERENCE BETWEEN FINDING DISTINCT PATHS AND NOT
        //let distinctPaths = Map.fold (fun s k v -> Map.add k (set [v]) s) Map.empty paths
        
        // Map of end locations and their corresponding train
        let gl = List.fold (fun s (t,_,l,_) -> Map.add l t s) Map.empty tl
        // Map of trains and their direction
        let ds = List.fold (fun s (t,_,_,d) -> Map.add t d s) Map.empty tl

        // Set of trains that in someway has to swap location with another train
        let swappers = Swappers tm gl

        // Set of trains in swap cycles
        let swapCycles = FindSwapCycles tm gl
        
        // Calculate priorities of the trains in swap cycles
        let priorities,x = PrioritiesSwapCycle swapCycles goal paths ds distanceMap
        
        // Find the highest priority so far
        let c = Map.fold (fun s k v -> max s v) 0 priorities
        
        // Set of train in swap non-cycles
        let nonCycles = Set.difference swappers (Set.fold (fun s v -> s + v) Set.empty swapCycles)

        // Set of trains not part of swap cycles
        let ts = (keySet tm) - (swappers - nonCycles)

        // Distinct path for only the swap cycle trains
        let swappersDistinctPaths = Set.fold (fun s v -> Map.remove v s) distinctPaths ts

        // Finding exact paths for swap cycles trains
        let swapPaths = SwapperPaths priorities (Set.unionMany (Set.toSeq swapCycles)) swappersDistinctPaths

        // Finding priority and exact path for train not part of swap cycles
        let priorities,p = PriorityFun tm ts goal distinctPaths priorities (c+Set.count ts) (swappers-nonCycles)
        let exactPaths = Map.fold (fun s k v -> Map.add k (Set.unionMany (Set.toSeq v)) s) Map.empty p

        // Adding exact path for trains part of swap cycles
        let finalPaths = Map.fold (fun s k v -> Map.add k v s) exactPaths swapPaths

        //Setting priority of trains with no open path to highest swapper
        let finalPriorities = Map.fold (fun m k v -> if not (Map.containsKey k m) then (Map.add k c m) else m) priorities tm

        //UNCOMMENT to see effect of priorities
        //let finalPriorities = Map.fold (fun s k v -> Map.add k 1 s) Map.empty priorities
        //let c = 1

        trains, rwgLeft, rwgRight, goal, distanceMap, finalPaths, sr, finalPriorities, c, sm,  S(0,sm,tm,rm,N)