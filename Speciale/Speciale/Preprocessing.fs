﻿namespace Railways

open Railways.Types
open FSharpx.Collections
open System

module Preprocess =

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
               let nm = Set.fold (fun s v -> Map.add (loc,v) c s) m nexts
               CreateDistanceMapLoc loc nexts (Set.union nexts explored) (c+1) nm rwg


    let CreateDistanceMap ll rwg = List.fold (fun m v -> CreateDistanceMapLoc v (set [v]) (set [v]) 1 (Map.add (v,v) 0 m) rwg) Map.empty ll


    // Found by taking intersection of reachable locations going train direction from starting location and the opposite direction from the gosl location
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

    // 
    let rec CalculatePriorities (pre:Map<Train,int>) (cur:Map<Train,int>) (tm:TrainMap) (gm:Map<Location,Train>) x =
        match pre = cur with
        | true -> cur
        | false -> let maxPrio = Map.count tm + x
                   let nm = Map.fold (fun s t l -> if Map.containsKey l gm && Map.containsKey t cur then Map.add t (min (Map.find (Map.find l gm) cur + 1) maxPrio) s else s) cur tm 
                   CalculatePriorities cur nm tm gm x

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
    let PrioritiesSwapCycle (ts:Set<Set<Train>>) (gm:TrainMap) (paths:Map<Train,Set<Location>>) (ds:Map<Train,Direction>) (dms:Map<Direction,DistanceMap>) =
        Set.fold (fun (sm,sc) v -> let l = Set.fold (fun sx t -> (PathDistance (Map.find t gm) (Map.find t paths) (Map.find (Map.find t ds) dms),t)::sx) [] v
                                   let sl = List.sortDescending l
                                   let ll,_ = List.fold (fun (sl,c) (_,t) -> Map.add t (c+sc) sl,(c+1)) (sm,1) sl
                                   (ll,sc+(Map.count gm))) (Map.empty,0) ts

    // TODO IMPORTANT : Check if moving a train to goal will block other train if so DO NOT DO IT
    let rec pfun (curLoc:Map<Train,Location>) (ts:Set<Train>) (gs:Map<Train,Location>) (paths:Map<Train,Set<Location>>) (pm:Map<Train,int>) (c:int) =
        match Set.isEmpty ts with
        | true  -> pm
        | false -> let freeTrain = Set.fold (fun s t -> let path = Map.find t paths
                                                        let x = Set.intersect (Set.remove (Map.find t curLoc) (Set.ofSeq (Map.values curLoc))) path
                                                        match Set.isEmpty x with
                                                        | true -> Set.add t s
                                                        | _ -> s) Set.empty ts
                   match Set.isEmpty freeTrain with
                   | true  -> pm
                   | false -> let t = Set.fold (fun s v -> let p = Map.find v paths
                                                           let x = Set.fold (fun sx vx -> let px = Map.find vx paths
                                                                                          if Set.isEmpty (Set.intersect p px) 
                                                                                          then Set.add vx sx
                                                                                          else sx) Set.empty freeTrain
                                                           let y = Set.add v x
                                                           Set.add y s) Set.empty freeTrain
                              let bts = Set.fold (fun s v -> if Set.count v > Set.count s then v else s) Set.empty t
                              let curLoc = Set.fold (fun s v -> Map.add v (Map.find v gs) s) curLoc bts
                              let ts = Set.fold (fun s v -> Set.remove v s) ts bts
                              let pm = Set.fold (fun s v -> Map.add v c s) pm bts
                              let c = c - 1
                              pfun curLoc ts gs paths pm c


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

        // Create the distance maps
        let distanceMapLeft = CreateDistanceMap ll rwgLeft
        let distanceMapRight = Map.fold (fun s (l1,l2) d -> Map.add (l2,l1) d s) Map.empty distanceMapLeft

        // Find all locations on all paths from start to end location for all trains
        // TODO : Save each unique path for smarter priority function
        let paths = FindPaths (Map.toList tm) trains rwgLeft rwgRight goal

        // Map of end locations and their corresponding train
        let gl = List.fold (fun s (t,_,l,_) -> Map.add l t s) Map.empty tl
        // Map of trains and their direction
        let ds = List.fold (fun s (t,_,_,d) -> Map.add t d s) Map.empty tl
        // Map to get distancemap from a direction
        let dms = Map.add L distanceMapLeft (Map.add R distanceMapRight Map.empty)


        // Set of trains that in someway has to swap location with another train
        let swappers = Swappers tm gl

        // Set of trains in swap cycles
        let swapCycles = FindSwapCycles tm gl

        // Set of train in swap non-cycles
        let nonCycles = Set.difference swappers (Set.fold (fun s v -> s + v) Set.empty swapCycles)

        // Calculate priorities of the trains in swap cycles
        let swapCyclePrio,x = PrioritiesSwapCycle swapCycles goal paths ds dms

        // Calculate prioritues of trains in swap non-cycles
        let prio = Set.fold (fun s t -> Map.add t (x+1) s) Map.empty nonCycles
        let nonCyclePrio = CalculatePriorities Map.empty prio tm gl x

        // Combine the swap cycle and non-cycle priorities
        let priorities = Map.fold (fun s k v -> Map.add k v s) nonCyclePrio swapCyclePrio

        // Find the highest priority so far
        let c = Map.fold (fun s k v -> max s v) 0 priorities


        // TODO : Priority order is not yet perfect, missing to check if putting trains on end location blocks for trains, smart path needed
        
        let ts = (Map.keySet tm) - swappers
        let priorities = pfun tm ts goal paths priorities (c+Set.count ts) 
        let priorities,_ = Map.fold (fun (m,coun) k v -> if not (Map.containsKey k m) then (Map.add k coun m,coun+1) else (m,coun)) (priorities,c+1) tm

        trains, rwgLeft, rwgRight, goal, distanceMapLeft, distanceMapRight, paths, sr, priorities, x, sm,  S(0,sm,tm,rm,N)