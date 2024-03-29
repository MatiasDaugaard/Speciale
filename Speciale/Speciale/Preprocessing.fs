﻿namespace Railways

open Railways.Types

//Module used for the preprocessing of the network data, to make the solving more efficient

module Preprocess =

    // Function to get the value set of a map
    let valueSet m =
        Map.fold (fun s _ v -> Set.add v s) Set.empty m

    // Function to get the key set of a map
    let keySet m =
        Map.fold (fun s k _ -> Set.add k s) Set.empty m

    // Used for creating the railway graph
    let addVertex ((l1,l2):Rail) (m:RailwayGraph) = 
        let ll = Map.find l1 m
        Map.add l1 (l2::ll) m


    // Calculates the distance from Location l in direction d to all other reachable locations
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

    // Creates the DistanceMap by going through all location and calculating their distances to all other reachable loactions
    let CreateDistanceMap ll rwg = List.fold (fun m v -> CreateDistanceMapLoc v (set [v]) (set [v]) 1 (Map.add (v,v) 0 m) rwg) Map.empty ll


    // Find all paths by taking intersection of reachable locations from starting location in train direction and the opposite direction from the goal location
    // Only used for non priority version
    let FindPaths tm trains left right goal =
        let rec Path d s =
            let rwg = match d with
                      | L -> left
                      | _ -> right
            let x = Set.fold (fun st v -> Set.union (Set.ofList (Map.find v rwg)) st) s s
            match x = s with
            | true -> x
            | _ -> Path d x

        List.fold (fun s (t,d) -> let sl = Map.find t tm
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
                                  

    // Find the trains that needs to swap locations
    // Outdated function, no longer needed
    (*
    let Swappers (tm:TrainMap) gm paths =
        Map.fold (fun s k v -> let glocs = (valueSet gm)
                               let sx = match Set.contains v glocs with
                                        | true -> let ot = Map.findKey (fun ot gl -> gl = v) gm
                                                  Set.add k (Set.add ot s) 
                                        | false -> s

                               let ps = Map.find k paths 
                               let ts = Set.remove k (keySet tm)
                               let locP = Set.fold (fun ls t -> Set.add (t,Map.find t tm, Map.find t gm) ls) Set.empty ts
                               let b = Set.forall (fun p -> Set.exists (fun (_,l1,l2) -> not (Set.contains l1 p && Set.contains l2 p)) locP) ps
                                                      
                               match b with
                               | true -> let ot = Set.fold (fun s (t,_,_) -> Set.add t s) Set.empty (Set.filter (fun (t,l1,l2) -> Set.forall (fun p -> Set.contains l1 p || Set.contains l2 p) ps) locP) 
                                         Set.add k (Set.union ot s) 
                               | false -> sx) Set.empty tm
    *)

    // Calculates if a given train is part of a swap cycle, and if so returns the swap cycle
    let rec SwapCycle (tm:TrainMap) gm t s  =
        let l = Map.find t tm 
        match (Map.tryFindKey (fun k v -> v = l) gm) with
        | Some(tr) -> match Set.contains tr s with
                            | true -> Set.add t s
                            | false -> SwapCycle tm gm tr (Set.add t s)
        | None -> Set.empty 

    // Calculates if any train is part of a special swap cycle, not chaging places but train would block if placed or not moved, and returns swap cycle
    let SpecialSwapCycle (tm:TrainMap) gm t paths = 
        let ps = Map.find t paths 
        let ts = Set.remove t (keySet tm)
        let locP = Set.fold (fun ls t -> Set.add (t,Map.find t tm, Map.find t gm) ls) Set.empty ts
        let b = Set.forall (fun p -> Set.exists (fun (_,l1,l2) -> not (Set.contains l1 p && Set.contains l2 p)) locP) ps
        match b with
        // true = No free path, therefore part of swapcycle, find other trains, also part of cycle
        | true -> let ot = Set.fold (fun s (t,_,_) -> Set.add t s) Set.empty (Set.filter (fun (t,l1,l2) -> Set.forall (fun p -> Set.contains l1 p || Set.contains l2 p) ps) locP) 
                  Set.add t ot
        // false = Has free path, therefore not part of swap cycle
        | false -> Set.empty

    // Combines sets of trains if they have any trains in common
    let rec CombineSwapSets ss rs = 
        match Set.isEmpty ss with
        | true -> rs
        | false when Set.isEmpty rs -> let s = Set.minElement ss
                                       CombineSwapSets (Set.remove s ss) (Set.add s rs)
        | false -> let x = Set.maxElement ss
                   let rest = (Set.remove x ss)
                   let rs = match Set.exists (fun v -> not (Set.isEmpty (Set.intersect v x))) rs with
                            | true -> Set.fold (fun s v -> if not (Set.isEmpty (Set.intersect v x)) then Set.add (v+x) s else Set.add v s) Set.empty rs
                            | false -> Set.add x rs
                   CombineSwapSets rest rs

    // Finds swap cycles in the network
    let rec FindSwapCycles (tm:TrainMap) gm paths =
        let nsc = Map.fold (fun s t l -> let cycle = (SwapCycle tm gm t Set.empty) 
                                         if Set.isEmpty cycle then s else Set.add cycle s) Set.empty tm
        let scs = Map.fold (fun s t l -> let cycle = SpecialSwapCycle tm gm t paths
                                         match Set.isEmpty cycle with
                                         | true -> s 
                                         | false -> Set.add cycle s) nsc tm
        Set.fold (fun s v -> if Set.count v < 2 then s else Set.add v s) Set.empty (CombineSwapSets scs Set.empty)

    // Function returning shortest path based on length and fewest vertical switches
    let shortestPath ps locs = 

        //Find the shortest of two paths
        let shortest p1 p2 = 
            match Set.isEmpty p1, Set.isEmpty p2 with
            | true,_ -> p2
            | _,true -> p1
            | _ -> let rec jumpCount l c = 
                       match l with
                       | [] -> c
                       | [x] -> c
                       | x::(y::rest) -> if abs (x-y) = 1 then jumpCount (y::rest) c else jumpCount (y::rest) (c+1)
                   let sp1 = List.sort (Set.toList p1)
                   let l1 = Set.count p1 + jumpCount sp1 0
                   let sp2 = List.sort (Set.toList p2)
                   let l2 = Set.count p2 + jumpCount sp2 0
                   if l1 <= l2 then p1 else p2

        let rec bestPath ps bp =
            match ps with
            | [] -> bp
            | x::xs when Set.isEmpty (Set.intersect locs x) -> bestPath xs (shortest bp x)
            | _::xs -> bestPath xs bp

        bestPath (Set.toList ps) Set.empty
        

    // Function returning if given location is safe, meaning all other trains have a path if something would block the location
    let LocationIsSafe l (ts:Set<Train>) (paths:Map<Train,Set<Set<Location>>>) =
        Set.forall (fun v -> let ps = Map.find v paths
                             Set.exists (fun ls -> not (Set.contains l ls)) ps) ts

    // Function to give priority to trains that have a free path to goal, and give trains that have non crossing path same priority recursively
    let rec CalculatePriorities (curLoc:Map<Train,Location>) (ts:Set<Train>) (gs:Map<Train,Location>) (fPaths:Map<Train,Set<Set<Location>>>) (comPaths:Map<Train,Set<Set<Location>>>) (pm:Map<Train,int>) (c:int) =
        match Set.isEmpty ts with
        | true  -> pm,fPaths
        | false -> // Temporarily remove paths that cannot be used due to locations of train
                   let tempPaths = Map.fold (fun s t v -> let locs = (Set.remove (Map.find t curLoc) (valueSet curLoc))
                                                          let ls = Set.fold (fun s v -> if Set.isEmpty (Set.intersect locs v) then Set.add v s else s ) Set.empty v
                                                          Map.add t ls s) Map.empty fPaths
                   // Find all trains the have an open path from start to goal, in current setup, and does not block trains by being in goal location
                   let freeTrain = Set.fold (fun s t -> let pathSet = Map.find t tempPaths
                                                        //Location of the other trains
                                                        let locs = (Set.remove (Map.find t curLoc) (valueSet curLoc))
                                                        //Checks if given train has a path that does not intersect with location of other trains
                                                        match Set.exists (fun path -> Set.isEmpty (Set.intersect locs path)) pathSet with
                                                        | true -> //Checks if putting train in goal blocks other from being able to get to goal
                                                                  let g = Map.find t gs
                                                                  match LocationIsSafe g (Set.remove t ts) comPaths with
                                                                  | true -> Set.add t s
                                                                  | _ -> s
                                                        | _ -> s) Set.empty ts
                   match Set.isEmpty freeTrain with
                   | true  -> pm,fPaths
                   | false -> //Finds lists of trains with open path, that have non crossing paths
                              let t = Set.fold (fun s v -> let pathSet = Map.find v tempPaths
                                                           // Location of other trains
                                                           let locs = (Set.remove (Map.find v curLoc) (valueSet curLoc))
                                                           // Find shortest paths that does not cross any other trains current position
                                                           let p = shortestPath pathSet locs
                                                           // Finds free trains that have non crossing paths with train
                                                           let (x,_) = Set.fold (fun (sx,xx) vx -> let px = Map.find vx tempPaths
                                                                                                   let gls = List.fold (fun s v -> Set.add (Map.find v gs) s) Set.empty (vx::sx)
                                                                                                   let py = Set.fold (fun sz vz -> let b1 = Set.isEmpty (Set.intersect vz xx)
                                                                                                                                   let b2 = (Set.count vz < Set.count sz || Set.isEmpty sz)
                                                                                                                                   if b1 && b2 then vz else sz
                                                                                                                     ) Set.empty px
                                                                                                   let b = Map.exists (fun mk mv -> let pss = Set.filter (fun ls -> Set.isEmpty (Set.intersect ls gls)) mv
                                                                                                                                    not (List.contains mk sx || mk = vx) && Set.isEmpty pss
                                                                                                                      ) comPaths
                                                                                                   if Set.isEmpty py || b
                                                                                                   then (if b && List.contains vx sx then ([],xx) else (sx,xx))
                                                                                                   else vx::sx,xx+py
                                                                                ) ([v],p) freeTrain
                                                           Set.add x s
                                               ) Set.empty freeTrain
                              //Pick the list with the most trains
                              let bts = Set.fold (fun s v -> if List.length v > List.length s then v else s) [] t
                              // If bts is empty return
                              if List.isEmpty bts 
                              then pm,fPaths
                              else 
                              let gls = List.fold (fun s v -> Set.add (Map.find v gs) s) Set.empty bts
                              //Update the path of the trains to the ones not crossing
                              let fPaths,_ = List.fold (fun (s,sp) v -> let locs = (Set.remove (Map.find v curLoc) (valueSet curLoc)) + sp
                                                                        let pathSet = Map.find v tempPaths
                                                                        let p = shortestPath pathSet locs
                                                                        (Map.add v (set [p]) s),sp+p) (fPaths,Set.empty) (List.rev bts) 
                              //Remove these paths from the comPaths
                              let comPaths = List.fold (fun s v -> let pss = Map.find v s
                                                                   let l = Map.find v curLoc
                                                                   let npss = Set.fold (fun sa va -> let ns = Set.difference va (Set.unionMany (Map.find v fPaths))
                                                                                                     Set.add ns sa) Set.empty pss
                                                                   Map.add v npss s
                                                       ) comPaths bts
                              //Remove the trains from the set of trains not in goal
                              let ts = List.fold (fun s v -> Set.remove v s) ts bts
                              //Remove all paths for other trains containing location of trains put in goal
                              let fPaths = Map.fold (fun s k v -> let pss = Set.filter (fun ls -> Set.isEmpty (Set.intersect ls gls)) v
                                                                  if Set.contains k ts then Map.add k pss s else s
                                                      ) fPaths fPaths
                              let comPaths = Map.fold (fun s k v -> let gls = Set.fold (fun s v -> Set.add (Map.find v gs) s) Set.empty (Set.remove k (Set.ofList bts))
                                                                    let pss = Set.filter (fun ls -> Set.isEmpty (Set.intersect ls gls)) v
                                                                    Map.add k pss s
                                                      ) comPaths comPaths
                              //Update location of trains, as if the just picked trains have been moved to their goal locations
                              let curLoc = List.fold (fun s v -> Map.add v (Map.find v gs) s) curLoc bts

                              //Give the trains a priority
                              let pm = List.fold (fun s v -> Map.add v c s) pm bts
                              let c = c - 1

                              CalculatePriorities curLoc ts gs fPaths comPaths pm c 



    // Finds all currently reachable locations from a train
    let PreReachableLocations (t:Train) tm (d:Direction) (paths:Map<Train,Set<Set<Location>>>) rwgL rwgR bl = 
        let l = Map.find t tm
        let path = Set.unionMany (Map.find t paths)
        let rwg = match d with
                  | R -> rwgR
                  | L -> rwgL
        let rec Locations (ls:Set<Location>) = 
            let nls = Set.fold (fun s p -> let y = Map.find p rwg
                                           let y = List.fold (fun s v -> if Set.contains v bl || not (Set.contains v path) then s else v::s) [] y
                                           let x = (List.fold (fun st va -> Set.add va st) Set.empty y)
                                           Set.union x s) ls ls
            match ls = nls with
            | true -> ls
            | _ -> Locations nls
        Locations (Set.ofList [l])
        

    //Find a train which can be move to the "side" safely
    let FindSafeTrain (ts:Set<Train>) (paths:Map<Train,Set<Set<Location>>>) dm tm sm td bl rwgL rwgR =
        //For each train find their "safe" locations
        let safeZone = Set.fold (fun s v -> // Find all locations the train can reach
                                            let bl = Set.union bl (Set.remove (Map.find v tm) (valueSet tm))
                                            let locs = PreReachableLocations v tm (Map.find v td) paths rwgL rwgR bl 
                                            // For each location check if is safe, meaning does not block other train from reaching goal
                                            let sls = Set.fold (fun ss l -> 
                                                                            match LocationIsSafe l (Set.remove v ts) paths with
                                                                            | true -> Set.add (v,l) ss
                                                                            | _ -> ss) Set.empty locs
                                            Set.union s sls
                                ) Set.empty ts
        //The the train with the longest distance to a safe location
        Set.fold (fun (d,tr,loc) (t,l) -> let dis = Map.find (l,Map.find t tm) dm
                                          let dir = Map.find t td
                                          let rwg = match dir with
                                                    | R -> rwgR
                                                    | L -> rwgL
                                          //Safe location needs a signal, such that the train does not move away from it
                                          match dis > d && ((Map.containsKey (l,dir) sm) || List.isEmpty (Map.find l rwg)) && dis > 0 with
                                          | true -> (dis,t,l)
                                          | _ -> (d,tr,loc)
                 ) (0,"",0) safeZone

    //Creates the extra goal map and paths map allowing trains to move to safe location to break swap-cycles
    let rec SplitWork swappers paths dm tm sm ds gml rwgL rwgR bl =
        let gm = List.head gml
        let ngm, dp, stl = Set.fold (fun (ngm,dp,ts) sc -> //Find train to park in safe location
                                                           let (_,t,l) = FindSafeTrain sc paths dm tm sm ds bl rwgL rwgR 
                                                           //Creating new temp goal for train
                                                           let ngm = Map.add t l ngm
                                                           //Find and update the distinct paths using the updated goal map for the safe train
                                                           let sdp = FindDistinctPaths tm ngm [(t,Map.find t ds)] rwgL rwgR
                                                           let dp = Map.fold (fun s k v -> Map.add k v s) dp sdp
                                                           (ngm,dp,(t,l)::ts)
                                    ) (gm,paths,[]) swappers
        //The trains just moved to safe locations
        let st = List.fold (fun s v -> fst v::s) [] stl
        let safeTs = Set.ofList st
        //Update paths for other train, to no longer being able to use ones where safe trains have been placed, and blocked location
        let bl,dp = List.fold (fun (ls,ps) (t,l) -> let d = Map.find t ds
                                                    let ts = Set.fold (fun s v -> if Map.find v ds <> d then Set.add v s else s) Set.empty (keySet tm)
                                                    let ndp = Set.fold (fun s v -> Map.add v (Map.find v dp) s) Map.empty ts
                                                    let nps = Map.fold (fun s k v -> let nv = Set.fold (fun s v -> match (Set.contains l v) with
                                                                                                                   | false ->  Set.add v s 
                                                                                                                   | true -> s) Set.empty v
                                                                                     Map.add k nv s) dp ndp
                                                    Set.add (l) ls,nps) (Set.empty,dp) stl
        //Remove the trains from the train map
        let tm = Set.fold (fun s v -> Map.remove v s) tm safeTs

        //Find if any more trains still need swapping
        let swappers = FindSwapCycles (tm:TrainMap) ngm dp
        match (Set.isEmpty swappers) with
        | true -> (ngm::gml,dp,st)
        | false -> SplitWork swappers dp dm tm sm ds (ngm::gml) rwgL rwgR bl
        

    // InitiateState creates the initial state and static global variables, given a railway network
    let InitiateState (ll,rl,srl,sl,tl) = 


        // Create the initial signal, train and switchrail maps, for the initial state
        let sm = List.fold (fun s v -> Map.add v false s) Map.empty sl
        let tm = List.fold (fun s (t,l,_,_) -> Map.add t l s) Map.empty tl
        let rm = List.fold (fun s (l1,l2,l3,d) -> (Map.add (l1,l2,l3,d) true) s) Map.empty srl
        let initialState = S(0,sm,tm,rm,N)

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


        // The block below should be uncommented if the priority preprocess should be used
        // #################################
        // START OF PRIORITY PREPROCESS CODE
        //(*
        // Find all distinct paths from start to end location for all trains
        let distinctPaths = FindDistinctPaths tm goal trains rwgLeft rwgRight

        // Map of trains and their direction
        let ds = List.fold (fun s (t,_,_,d) -> Map.add t d s) Map.empty tl

        // Set of trains in swap cycles
        let swapCycles = FindSwapCycles tm goal distinctPaths

        //Find the trains which has to be move to safe locations first round
        let goals,dPaths,sts = SplitWork swapCycles distinctPaths distanceMap tm sm ds [goal] rwgLeft rwgRight Set.empty

        let goalFirst = List.head goals
        let goalLast = List.last goals

        //Find paths for second part of trains routes, needed to avoid placing blocking trains in first pass
        let sptm = Map.fold (fun s k v -> if List.contains k sts then Map.add k (Map.find k goalFirst) s else s) Map.empty tm
        let spTrains = List.fold (fun s (t,d) -> if List.contains t sts then (t,d)::s else s ) [] trains
        let spPaths = FindDistinctPaths sptm goalLast spTrains rwgLeft rwgRight

        let disPaths = Map.fold (fun s k v -> let fps = Map.find k s
                                              let sps = v
                                              let nps = Set.fold (fun sa va -> let x = Set.fold (fun sb vb -> Set.add (va+vb) sb
                                                                                                ) Set.empty sps
                                                                               Set.union x sa
                                                                 ) Set.empty fps
                                              Map.add k nps s
                                ) dPaths spPaths
        let ts = (keySet tm)


        // Finding priority and exact path for trains
        let priorities,p = CalculatePriorities tm ts goalFirst dPaths disPaths Map.empty (Set.count ts)
        // Find train that block paths if places first pass
        let blockers = Map.fold (fun s k v -> if Map.containsKey k priorities then s else Set.add k s) Set.empty p
        // Set the paths for the train to the paths taken first pass
        let firstPaths = Map.fold (fun s k v -> if Set.contains k blockers then Map.add k (set[Map.find k tm]) s else Map.add k (Set.unionMany (v)) s) Map.empty p
        // Update the goal for blockers first path
        let firstGoal = Set.fold (fun s v -> Map.add v (Map.find v tm) s) goalFirst blockers
        let goals = [firstGoal;goalLast]
        // For second pass find the paths for the trains at safe locations or trains that was blocking first round to their goals
        let sptm = Map.fold (fun s k v -> Map.add k (Map.find k goalFirst) s) tm priorities
        let spgm = goalLast
        let spdp = FindDistinctPaths sptm spgm trains rwgLeft rwgRight
        

        let x,np = CalculatePriorities sptm ts spgm spdp spdp Map.empty (Set.count ts)
        let nps = Map.fold (fun s k v -> Map.add k (Set.unionMany (v)) s) Map.empty np
        let Paths = firstPaths::[nps]
        let priorities = Map.fold (fun s k v -> if Map.containsKey k s then s else Map.add k v s) priorities x
        //TODO : No train should not have been given a priority, so if used some case not covered
        let finalPriorities = Map.fold (fun m k v -> if not (Map.containsKey k m) then (Map.add k 0 m) else m) priorities tm
        // END OF PRIORITY PREPROCESS CODE
        // ###############################
        //*)


        //The block below should be uncommented if the version of no priorities should be used
        (*
        // ####################################
        // START OF NO PRIORITY PREPROCESS CODE
        let goals = [goal]
        let paths = FindPaths tm trains rwgLeft rwgRight goal
        let Paths = [paths]
        let finalPriorities = Map.fold (fun m k v -> Map.add k 0 m) Map.empty tm
        // END OF NO PRIORITY PREPROCESS CODE
        // ##################################
        *)

        trains, rwgLeft, rwgRight, goals, distanceMap, Paths, sr, finalPriorities, 0, sm,  initialState