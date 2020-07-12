namespace Railways

open Railways.Types
open Railways.Preprocess

module Postprocess =

    // Gets the location of a given train in a given state
    let GetTrainLocation s t =
        match s with
        | S(_,sm,tm,rm,p) -> Map.find t tm
        | N -> failwith "N state in solution"

    // Gets the direction of a train
    let GetTrainDirection t tdl =
        snd (List.find (fun (tr,d) -> tr = t) tdl)

    // Gets the TrainMap from a state
    let GetTrainMap s =
        match s with
        | S(_,sm,tm,rm,p) -> tm
        | N -> failwith "N state in solution"

    // Gets the SignalMap from a state
    let GetSignalMap s =
        match s with
        | S(_,sm,_,_,_) -> sm
        | N -> failwith "N state in solution"

    // Gets the SwitchRailMap from a state
    let GetSwitchRailMap s =
        match s with
        | S(_,_,_,rm,_) -> rm
        | N -> failwith "N state in solution"

    // Returns a signal map with the signal a given location turned of, if signal is there
    let TurnOffSignal l sm =
        let nsm = match Map.tryFind (l,R) sm with
                  | Some(_) -> Map.add (l,R) false sm
                  | None -> sm
        match Map.tryFind (l,L) nsm with
        | Some(_) -> Map.add (l,L) false nsm
        | None -> nsm

    // Changes the signal map of a state              
    let ChangeSignalMap s sm =
        match s with
        | S(h,_,tm,rm,p) -> S(h,sm,tm,rm,p)
        | _ -> failwith "N in ChangeSignalMap"


    // Function to turn of signals when train has passed signal
    let rec TurnOffSignals sl nsl als = 
        match sl with
        | [] -> nsl
        | x::xs when List.isEmpty nsl -> TurnOffSignals xs (x::nsl) als
        | x::xs -> let curTM = GetTrainMap x
                   let lastTM = GetTrainMap (List.head nsl )
                   let ls = Map.fold (fun s k v -> if v <> Map.find k lastTM then Set.add (Map.find k lastTM) s else s) Set.empty curTM
                   match Set.isEmpty ls with
                   | true -> TurnOffSignals xs (x::nsl) Set.empty
                   | false -> let cls = Set.union als ls
                              let sm = GetSignalMap x
                              let nsm = Set.fold (fun s v -> TurnOffSignal v s) sm cls 
                              let ns = ChangeSignalMap x nsm
                              TurnOffSignals xs (ns::nsl) cls

    // Splits the state list into list of order of trains moving
    let rec SplitStateList sl nsl ssl rsl = 
        match sl with
        | [] -> List.rev rsl
        | x::xs -> let sm = GetSignalMap x
                   let nsm = GetSignalMap (List.head nsl)
                   match sm = nsm with
                   | true -> let rl = List.head rsl
                             let nrl = (List.head ssl)::rl
                             SplitStateList xs (x::nsl) (List.tail ssl) (nrl::(List.tail rsl))
                   | false -> SplitStateList xs (x::nsl) (List.tail ssl) ([List.head ssl]::rsl)

    // Function to find which locations are in use in a state list
    let rec GetImportantLocations sl locs = 
        match sl with
        | [] -> locs
        | x::[] -> locs
        | x::(y::rest) -> let tm1 = GetTrainMap x
                          let tm2 = GetTrainMap y
                          let locs = Map.fold (fun s k v -> if Map.find k tm2 <> v then Set.add v (Set.add (Map.find k tm2) s) else s) locs tm1
                          GetImportantLocations (y::rest) locs

    // Find the train that are moving in the state list
    let rec GetTrains sl ts = 
        match sl with
        | [] -> ts
        | x::[] -> ts
        | x::(y::rest) -> let tm1 = GetTrainMap x
                          let tm2 = GetTrainMap y
                          let locs = Map.fold (fun s k v -> if Map.find k tm2 <> v then Set.add k s else s) ts tm1
                          GetTrains (y::rest) locs

    // Find splitpoint in list where the states can merge
    let rec FindSplitState sl locs ts rsl = 
        match sl with 
        | [] -> sl,rsl
        | x::xs -> let sm = GetSignalMap x
                   let tm = GetTrainMap x 
                   let tlocs = Set.fold (fun s v -> Set.add (Map.find v tm) s) Set.empty ts
                   let b = Map.exists (fun (l,d) v -> (Set.contains l locs && v)) sm
                   match b || not (Set.isEmpty (Set.intersect locs tlocs)) with
                   | true -> FindSplitState xs locs ts (x::rsl)
                   | false -> sl,rsl

    // Updates a state by changing the signal map, train map and switchrail map
    let UpdateState s sm tm rm = 
        match s with
        | S(h,_,_,_,p) -> S(h,sm,tm,rm,p)
        | N -> N


    // Merges two state list together by merging the signal, train and switchrail maps at given locations
    let rec Merge sl msl rsl locs =
        match sl with
        | [] -> List.fold (fun s v -> v::s) rsl msl
        | _ when List.isEmpty msl -> match List.isEmpty sl with
                                     | true -> rsl 
                                     | false -> let nsl = List.init (List.length sl) (fun v -> List.head rsl)
                                                let nmsl = sl
                                                let nrsl = rsl
                                                let ts = GetTrains nmsl Set.empty
                                                let tlocs = Set.fold (fun s v -> Set.add (GetTrainLocation (List.head rsl) v) s) Set.empty ts
                                                let nlocs = (tlocs) + (GetImportantLocations nmsl Set.empty)
                                                Merge nsl nmsl nrsl nlocs
        | x::xs -> let sm = GetSignalMap x
                   let tm = GetTrainMap x
                   let rm = GetSwitchRailMap x

                   let ms = List.head msl 

                   let nsm = Map.fold (fun s k v -> if Set.contains (fst k) locs then Map.add k v s else s) sm (GetSignalMap ms)
                   let ntm = Map.fold (fun s k v -> if Set.contains v locs then Map.add k v s else s) tm (GetTrainMap ms)
                   let nrm = Map.fold (fun s (l1,l2,l3,d) v -> if (Set.contains l1 locs || Set.contains l2 locs || Set.contains l3 locs) then Map.add (l1,l2,l3,d) v s else s) rm (GetSwitchRailMap ms) 

                   let ns = UpdateState x nsm ntm nrm 
                   Merge xs (List.tail msl) (ns::rsl) locs

    // Merges the second element (list) of the list into the first, updates the second element and recurse over the tial of the list
    let rec Merging l r = 
        match l with
        | [] -> r
        | x::[] -> x@r
        | x::y::rest -> // Get the state list that should have something merged into it
                        let sl = List.rev x
                        // Get the state list that should be merged into sl
                        let msl = List.rev y
                        // Find the location which trains are using in msl
                        let locs = GetImportantLocations msl Set.empty
                        // Find the trains that are moving in sl
                        let n = min (List.length sl) (List.length msl)
                        let ts = GetTrains (List.rev(List.take n (List.rev sl))) Set.empty
                        // Find the place to merge into sl
                        let sl1, rsl = FindSplitState sl locs ts []
                        // Put the non-mergeable states in the result list
                        let r = rsl@r
                        // Merge msl into the place in sl
                        let rsl1 = Merge sl1 msl r locs
                        let ny = (List.take (List.length y) rsl1)
                        let nrsl = List.rev (List.take (List.length rsl1 - List.length y) (List.rev rsl1))
                        Merging (ny::rest) nrsl

    // Find the point at which the solution can be split then merges the lists together
    let MergeStates sl ssl = 
        let x = SplitStateList (List.tail sl) ([List.head sl]) (List.tail ssl) [[List.head ssl]]
        //First element always initial state, which should be kept unmerged
        let r = List.head x
        Merging (List.tail x) r
        


    // Postprocess function for solution found using the opening of entire paths function
    let CombineSolutionEntirePath sl =
        let slr = List.rev sl
        let r = TurnOffSignals slr [] Set.empty
        let rr = (List.rev r)
        MergeStates slr rr

    // Check if any signal is on is a signalmap
    let SignalIsOn sm = 
        Set.exists (fun v -> v) (valueSet sm)

    let NewSignalOn smx smy =
        Map.fold (fun s k v -> let b = Map.find k smy
                               if b && b<>v then true else s) false smx

    
    // Finds trains that have moved/changed position in a list of states
    let rec GetMovingTrains sl rts = 
        match sl with 
        | [] -> rts 
        | [_] -> rts 
        | x::y::rest -> let tmx = GetTrainMap x
                        let tmy = GetTrainMap y
                        let smx = GetSignalMap x
                        let smy = GetSignalMap y
                        let locs = Map.fold (fun s k v -> if v || Map.find k smy then Set.add (fst k) s else s) Set.empty smx
                        let ts = (Map.fold (fun s k v -> if v <> Map.find k tmx || Set.contains v locs || Set.contains (Map.find k tmx) locs then Set.add k s else s) rts tmy)
                        GetMovingTrains (y::rest) ts
                        

    // Find the consequetive set of states for which a set of trains are moving
    let rec GetMovingTrainsStates ts sl rsl tdl = 
        match sl with
        | [] -> [],rsl
        | [x] -> [],x::rsl
        | x::y::xs -> let mts = GetMovingTrains (x::[y]) Set.empty
                      match mts = ts with
                      | true -> GetMovingTrainsStates ts (y::xs) (x::rsl) tdl
                      | false -> sl,x::rsl


    // Splits a state list into states list containing set of trains moving
    let rec SplitStateListSingleStep sl asl tdl = 
        match sl with
        | [] -> List.rev asl
        | x::y::xs -> let ts = GetMovingTrains (x::[y]) Set.empty
                      let nsl,rsl = GetMovingTrainsStates ts (y::xs) [x] tdl
                      SplitStateListSingleStep nsl ((List.rev rsl)::asl) tdl
        | _ -> failwith "F"

    let rec GetNextLocations sl ts tdl locs rsl = 
        match sl with
        | [] -> locs,List.rev rsl
        | x::xs -> let tm = GetTrainMap x
                   let sm = GetSignalMap x
                   let ls = Set.fold (fun s t -> Set.add (Map.find t tm) s) Set.empty ts
                   let b = Set.exists (fun t -> let l = Map.find t tm
                                                let d = GetTrainDirection t tdl
                                                match Map.tryFind (l,d) sm with
                                                | Some(x) when x -> true
                                                | Some(_) -> false
                                                | None -> true) ts
                   match b with
                   | true -> GetNextLocations xs ts tdl (locs+ls) (x::rsl)
                   | false -> locs + ls,List.rev (x::rsl)

    let rec FindSplitStateSingleStep sl locs ts rsl = 
        match sl with
        | [] -> sl,rsl
        | x::xs -> let tm = GetTrainMap x
                   let ls = Set.fold (fun s v -> Set.add (Map.find v tm) s) Set.empty ts + (Map.fold (fun s (k,_) v -> if v then Set.add k s else s) Set.empty (GetSignalMap x))
                   match Set.isEmpty (Set.intersect ls locs) with
                   | false -> let ntm = match rsl with
                                        | [] -> tm
                                        | y::ys -> Set.fold (fun s v -> Map.add v (Map.find v tm) s) (GetTrainMap y) ts
                              let sm = GetSignalMap x
                              let rm = GetSwitchRailMap x
                              let ns = UpdateState x sm ntm rm
                              FindSplitStateSingleStep xs locs ts (ns::rsl)
                   | true -> let b = List.forall (fun v -> let tm = GetTrainMap v
                                                           let ls = Set.fold (fun s v -> Set.add (Map.find v tm) s) Set.empty ts
                                                           Set.isEmpty (Set.intersect ls locs)) xs
                             match b with
                             | false -> let ntm = match rsl with
                                                  | [] -> tm
                                                  | y::ys -> Set.fold (fun s v -> Map.add v (Map.find v tm) s) (GetTrainMap y) ts
                                        let sm = GetSignalMap x
                                        let rm = GetSwitchRailMap x
                                        let ns = UpdateState x sm ntm rm
                                        FindSplitStateSingleStep xs locs ts (ns::rsl)
                             | true -> sl, rsl

    let rec MergeSingleStep sl msl rsl ts = 
        match sl with
        | [] -> [],List.fold (fun s v -> v::s) rsl msl
        | x::xs -> match msl with
                   | [] -> sl,rsl
                   | y::ys -> let smx = GetSignalMap x
                              let tmx = GetTrainMap x
                              let rmx = GetSwitchRailMap x

                              let smy = GetSignalMap y
                              let tmy = GetTrainMap y
                              let rmy = GetSwitchRailMap y

                              let locs = Set.fold (fun s v -> Set.add (Map.find v tmy) s) Set.empty ts
                              let nsm = Map.fold (fun s k v -> if Set.contains (fst k) locs then Map.add k v s else s) smx smy
                              let ntm = Map.fold (fun s k v -> if Set.contains v locs then Map.add k v s else s) tmx tmy
                              let nrm = Map.fold (fun s (l1,l2,l3,d) v -> if (Set.contains l1 locs || Set.contains l2 locs || Set.contains l3 locs) then Map.add (l1,l2,l3,d) v s else s) rmx rmy 

                              let ns = UpdateState x nsm ntm nrm 
                              MergeSingleStep xs (List.tail msl) (ns::rsl) ts

    let rec StatesWithoutTrains sl ts =
        match sl with
        | [] -> []
        | x::xs -> let mts = GetMovingTrains (sl) Set.empty
                   match Set.isEmpty (Set.intersect ts mts) with
                   | true -> sl
                   | false -> StatesWithoutTrains xs ts 

    let rec MergingSingleStep l r tdl = 
        match l with
        | [] -> r
        | x::[] -> x@r
        | x::y::rest -> // Get the state list that should have something merged into it
                        let sl = x
                        // Get the state list that should be merged into sl
                        let msl = y

                        // Get the trains moving in sl
                        let s = if List.isEmpty r then List.head sl else List.head r
                        let ts = GetMovingTrains (sl) Set.empty
                        let allTs = List.fold (fun s (v,_) -> Set.add v s) Set.empty tdl
                        match ts = allTs with
                        | true -> let nx = List.tail sl
                                  let nr = (List.head sl::r)
                                  MergingSingleStep (nx::y::rest) nr tdl
                        | false ->  // Get the trains moving in msl
                                    let mts = GetMovingTrains msl Set.empty
                                    let a = if Set.contains "T0" mts
                                            then
                                                0
                                            else 
                                                1
                                    // Get the locations that are used for the next train ride in msl, and the states it is moving in
                                    let locs,ms = GetNextLocations msl mts tdl Set.empty []

                                    let ats = List.fold (fun s (v,_) -> if Set.contains v mts then s else Set.add v s) Set.empty tdl
                                    // Find the place to merge into sl TODO : Look at function
                                    let sl1, rsl = FindSplitStateSingleStep sl locs (ats) r
                                    // Put the non-mergeable states in the result list
                                    let r = rsl
                                    // Merge ms into sl, nsl = part of sl that has not been merged into rsl1 the merge lists
                                    let nsl,rsl1 = MergeSingleStep sl1 ms r mts
                                    // Get the part of the list msl that is not yet merged
                                    let nmsl = List.rev (List.take (List.length y - List.length ms) (List.rev y))
                                    match nsl,nmsl with
                                    | [],[] -> match rest with
                                               | [] -> rsl1
                                               | z::zs -> let ny = StatesWithoutTrains (List.rev rsl1) (GetMovingTrains z Set.empty)
                                                          let nrsl = List.rev (List.take (List.length rsl1 - List.length ny) (List.rev rsl1))
                                                          MergingSingleStep (ny::z::zs) nrsl tdl

                                    | [],_ -> let nrsl = List.fold (fun s v -> v::s) rsl1 nmsl 
                                              match rest with
                                              | [] -> nrsl
                                              | z::zs -> let ny = StatesWithoutTrains (List.rev nrsl) (GetMovingTrains z Set.empty)
                                                         let nrsl = List.rev (List.take (List.length nrsl - List.length ny) (List.rev nrsl))
                                                         MergingSingleStep (ny::z::zs) nrsl tdl
                                    | _,[] -> let nmsl1 = List.init (List.length nsl) (fun v -> List.head rsl1)
                                              let nsl1 = nsl
                                              let _,nrsl = MergeSingleStep nsl1 nmsl1 rsl1 mts
                                              match rest with
                                              | [] -> nrsl
                                              | z::zs -> let ny = StatesWithoutTrains (List.rev nrsl) (GetMovingTrains z Set.empty)
                                                         let nrsl = List.rev (List.take (List.length nrsl - List.length ny) (List.rev nrsl))
                                                         MergingSingleStep (ny::z::zs) nrsl tdl 
                                    | _,_ -> MergingSingleStep (nsl::nmsl::rest) rsl1 tdl
                                


    let MergeStatesSingleStep sl tdl =
        let x = SplitStateListSingleStep sl [] tdl
        let y = MergingSingleStep x [] tdl
        y


    let CombineSolutionSingleStep sl tdl =
        let slr = List.rev sl
        let r = TurnOffSignals slr [] Set.empty
        let rr = List.rev r
        let r = MergeStatesSingleStep rr tdl 
        r