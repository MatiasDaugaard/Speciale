﻿namespace Railways

open Railways.Types

module Postprocess =

    // Gets the location of a given train in a given state
    let GetTrainLocation s t =
        match s with
        | S(_,sm,tm,rm,p) -> Map.find t tm
        | N -> failwith "N state in solution"

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
        match Map.tryFind (l,R) sm with
        | Some(_) -> Map.add (l,R) false sm
        | None -> match Map.tryFind (l,L) sm with
                  | Some(_) -> Map.add (l,L) false sm
                  | None -> sm

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

    let UpdateState s sm tm rm = 
        match s with
        | S(h,_,_,_,p) -> S(h,sm,tm,rm,p)
        | N -> N

    let rec Merge sl msl rsl locs =
        match sl with
        | [] -> List.fold (fun s v -> v::s) rsl msl
        | _ when List.isEmpty msl -> rsl
        | x::xs -> let sm = GetSignalMap x
                   let tm = GetTrainMap x
                   let rm = GetSwitchRailMap x

                   let ms = List.head msl 
                    
                   let nsm = Map.fold (fun s k v -> if v then Map.add k v s else s) sm (GetSignalMap ms)
                   let ntm = Map.fold (fun s k v -> if Set.contains v locs then Map.add k v s else s) tm (GetTrainMap ms)
                   let nrm = Map.fold (fun s (l1,l2,l3,d) v -> if (Set.contains l1 locs || Set.contains l2 locs || Set.contains l3 locs) then Map.add (l1,l2,l3,d) v s else s) rm (GetSwitchRailMap ms) 

                   let ns = UpdateState x nsm ntm nrm 
                   Merge xs (List.tail msl) (ns::rsl) locs

    let rec Merging l r = 
        match l with
        | [] -> r
        | x::[] -> x@r
        | x::y::rest -> let sl = List.rev x
                        let msl = List.rev y
                        let locs = GetImportantLocations msl Set.empty
                        let ts = GetTrains sl Set.empty
                        let sl1, rsl = FindSplitState sl locs ts []
                        let r = rsl@r
                        let rsl1 = Merge sl1 msl r locs
                        let ny = (List.take (List.length y) rsl1)
                        let nrsl = List.rev (List.take (List.length rsl1 - List.length y) (List.rev rsl1))
                        Merging (ny::rest) nrsl

    let MergeStates sl ssl = 
        let x = SplitStateList (List.tail sl) ([List.head sl]) (List.tail ssl) [[List.head ssl]]
        let r = List.head x
        Merging (List.tail x) r
        


    // Postprocess function for solution found using the opening of entire paths function
    let CombineSolutionEntirePath sl ts  =
        let slr = List.rev sl
        let r = TurnOffSignals slr [] Set.empty
        let rr = (List.rev r)
        let mr = MergeStates slr rr
        


        let a = 0
        mr