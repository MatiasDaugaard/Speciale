namespace Railways

open Railways.Types

module Preprocess =

    
    // PREPROCCESSING PART

    // Used for creating the railway graph
    let addVertex ((l1,l2):Rail) (m:RailwayGraph) = 
        let ll = Map.find l1 m
        Map.add l1 (l2::ll) m


    // Distance from Location l in direction d to all other reachable locations
    let rec CreateDistanceMapLoc (loc:Location) (currentLocations:Set<Location>) (explored:Set<Location>) c m rwg =
        match Set.isEmpty currentLocations with
        | true -> m
        | _ -> let nexts = Set.difference (Set.fold (fun s v -> Set.ofList (Map.find v rwg) + s) Set.empty currentLocations) explored
               let nm = Set.fold (fun s v -> Map.add (loc,v) c s) m nexts
               CreateDistanceMapLoc loc nexts (Set.union nexts explored) (c+1) nm rwg


    let CreateDistanceMap ll rwg = List.fold (fun s v -> CreateDistanceMapLoc v (set [v]) (set [v]) 1 (Map.add (v,v) 0 s) rwg) Map.empty ll 


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





    // InitiateState creates the initial state given a railway network, and sets static variables
    // Type : RailwayNetwork -> State
    let InitiateState (ll,rl,srl,sl,tl) = 

        let sm = List.fold (fun s v -> Map.add v false s) Map.empty sl
        let tm = List.fold (fun s (t,l,_,_) -> Map.add t l s) Map.empty tl
        let rm = List.fold (fun s (l1,l2,l3,d) -> (Map.add (l1,l2) true) (Map.add (l1,l3) false s)) Map.empty srl
        let rwg = List.fold (fun s l -> Map.add l [] s) Map.empty ll

        let rwgRight1 = List.fold (fun s r -> addVertex r s) rwg rl
        let rwgRight2 = List.fold (fun s (l1,l2,l3,d) -> if d = R then addVertex (l1,l2) (addVertex (l1,l3) s) else addVertex (l2,l1) (addVertex (l3,l1) s)) rwgRight1 srl

        let rwgLeft1 = List.fold (fun s (l1,l2) -> addVertex (l2,l1) s) rwg rl
        let rwgLeft2 = List.fold (fun s (l1,l2,l3,d) -> if d = L then addVertex (l1,l2) (addVertex (l1,l3) s) else addVertex (l2,l1) (addVertex (l3,l1) s)) rwgLeft1 srl

        let trains = List.rev (List.fold (fun s (t,_,_,d) -> (t,d)::s) [] tl)
        let rwgLeft = rwgLeft2
        let rwgRight = rwgRight2
        let goal = (List.fold (fun s (t,_,l,_) -> Map.add t l s) Map.empty tl)
        let distanceMapLeft = CreateDistanceMap ll rwgLeft
        let distanceMapRight = CreateDistanceMap ll rwgRight
        let paths = FindPaths (Map.toList tm) trains rwgLeft rwgRight goal
        trains, rwgLeft, rwgRight, goal, distanceMapLeft, distanceMapRight, paths, S(0,sm,tm,rm,N,Set.empty)