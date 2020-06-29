namespace Railways

open Railways.Types

module Postprocess =

    // Gets the location of a given train in a given state
    let GetTrainLocation s t =
        match s with
        | S(_,sm,tm,rm,p) -> Map.find t tm
        | N -> failwith "N state in solution"

    // Gets the TrainMap from a state
    let GetTrainLocations s =
        match s with
        | S(_,sm,tm,rm,p) -> tm
        | N -> failwith "N state in solution"

    // Gets the TrainMap from a state
    let GetSignalMap s =
        match s with
        | S(_,sm,_,_,_) -> sm
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
        | x::xs -> let curTM = GetTrainLocations x
                   let lastTM = GetTrainLocations (List.head nsl )
                   let ls = Map.fold (fun s k v -> if v <> Map.find k lastTM then Set.add (Map.find k lastTM) s else s) Set.empty curTM
                   match Set.isEmpty ls with
                   | true -> TurnOffSignals xs (x::nsl) Set.empty
                   | false -> let cls = Set.union als ls
                              let sm = GetSignalMap x
                              let nsm = Set.fold (fun s v -> TurnOffSignal v s) sm cls 
                              let ns = ChangeSignalMap x nsm
                              TurnOffSignals xs (ns::nsl) cls

                   
    // Postprocess function for solution found using the opening of entire paths function
    let CombineSolutionEntirePath sl ts =
        let slr = List.rev sl
        let r = TurnOffSignals slr [] Set.empty
        let a = 0
        r