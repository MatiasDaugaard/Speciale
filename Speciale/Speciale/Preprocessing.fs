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
    // TODO : Look at this
    let PrioritiesSwapCycle (ts:Set<Set<Train>>) (gm:TrainMap) (paths:Map<Train,Set<Location>>) (ds:Map<Train,Direction>) (dm:DistanceMap) =
        Set.fold (fun (sm,sc) v -> let l = Set.fold (fun sx t -> (PathDistance (Map.find t gm) (Map.find t paths) dm,t)::sx) [] v
                                   //let l = Set.fold (fun sx t -> (Set.count (Map.find t paths),t)::sx) [] v
                                   let sl = (List.sortDescending l)
                                   let ll,_ = List.fold (fun (sl,c) (_,t) -> Map.add t (c+sc) sl,(c+1)) (sm,1) sl
                                   (ll,sc+(Map.count gm))) (Map.empty,0) ts

    let LocationIsSafe l (ts:Set<Train>) (paths:Map<Train,Set<Set<Location>>>) =
        Set.forall (fun v -> let ps = Map.find v paths
                             Set.exists (fun ls -> not (Set.contains l ls)) ps) ts

    // Function to give priority to trains that have a free path to goal, and give trains that have non crossing path same priority
    let rec PriorityFun (curLoc:Map<Train,Location>) (ts:Set<Train>) (gs:Map<Train,Location>) (paths:Map<Train,Set<Set<Location>>>) (pm:Map<Train,int>) (c:int) =
        match Set.isEmpty ts with
        | true  -> pm,paths
        | false -> // Find all trains the have an open path from start to goal, in current setup, and does not block trains by being in goal location
                   let freeTrain = Set.fold (fun s t -> let pathSet = Map.find t paths
                                                        //Location of the other trains
                                                        let locs = (Set.remove (Map.find t curLoc) (valueSet curLoc))
                                                        //Checks if given train has a path that does not intersect with location of other trains
                                                        match Set.exists (fun path -> Set.isEmpty (Set.intersect locs path)) pathSet with
                                                        | true -> //Checks if putting train in goal blocks other from being able to get to goal
                                                                  //TODO : Fix cuase broken
                                                                  let g = Map.find t gs
                                                                  (*
                                                                  let allPaths = Set.fold (fun s v -> let ps = Map.find v paths
                                                                                                      let p = Set.fold (fun sx vx -> sx+vx) Set.empty ps
                                                                                                      if v <> t then p+s else s) Set.empty (ts+swaps)
                                                                  *)
                                                                  match LocationIsSafe g (Set.remove t ts) paths with
                                                                  | true -> Set.add t s
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

                              PriorityFun curLoc ts gs paths pm c 
                              

    

    let FindSafeTrain (ts:Set<Train>) (paths:Map<Train,Set<Set<Location>>>) dm tm sm td =
        let safeZone = Set.fold (fun s v -> let locs = Set.unionMany (Map.find v paths)
                                            let sls = Set.fold (fun ss l -> match LocationIsSafe l (Set.remove v ts) paths with
                                                                            | true -> Set.add (v,l) ss
                                                                            | _ -> ss) Set.empty locs
                                            Set.union s sls
                                ) Set.empty ts
        Set.fold (fun (d,tr,loc) (t,l) -> let dis = Map.find (l,Map.find t tm) dm
                                          let dir = Map.find t td
                                          match dis < d && (Map.containsKey (l,dir) sm)with
                                          | true -> (dis,t,l)
                                          | _ -> (d,tr,loc)
                 ) (1000,"",0) safeZone



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

        //TODO : Work for more swap cycles and also not crash for networks without swap cycles
        let goals,dPaths,fp = if not (Set.isEmpty swapCycles) 
                                then 
                                    let (_,t,l) = FindSafeTrain (Set.minElement swapCycles) distinctPaths distanceMap tm sm ds
                                    let goals = [goal]
                                    let goal = Map.add t l goal
                                    //TODO : Fix the below to look nice
                                    let gs = (goal::goals)
                                    let dp = FindDistinctPaths tm goal trains rwgLeft rwgRight
                                    let fp = Map.fold (fun s k v -> Map.add k (Set.unionMany (v)) s) Map.empty distinctPaths
                                    let fp1 = Map.add t (Set.difference (Map.find t fp) (Set.unionMany (Map.find t dp))) fp
                                    let fp2 = Map.add t (Set.add l (Map.find t fp1)) fp1
                                    gs,dp,[fp2]
                                else
                                    [goal],distinctPaths,[]

        let ts = (keySet tm)

        let goalFinal = List.head goals
        // Finding priority and exact path for train not part of swap cycles
        let priorities,p = PriorityFun tm ts goalFinal dPaths Map.empty (Set.count ts)
        let finalPaths = Map.fold (fun s k v -> Map.add k (Set.unionMany (v)) s) Map.empty p
        //TODO : One distinct path for selected train t
        let finalPathss = finalPaths::fp

        //Setting priority of trains with no open path to highest swapper
        let finalPriorities = Map.fold (fun m k v -> if not (Map.containsKey k m) then (Map.add k 0 m) else m) priorities tm

        //UNCOMMENT to see effect of priorities
        //let finalPriorities = Map.fold (fun s k v -> Map.add k 1 s) Map.empty priorities
        //let c = 1

        trains, rwgLeft, rwgRight, goals, distanceMap, finalPathss, sr, finalPriorities, 0, sm,  S(0,sm,tm,rm,N)