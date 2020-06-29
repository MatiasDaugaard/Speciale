namespace Railways

open Railways.Types

module Postprocess =

    let GetTrainLocation s t =
        match s with
        | S(_,sm,tm,rm,p) -> Map.find t tm
        | N -> failwith "N state in solution"

    let GetSignalMap s =
        match s with
        | S(_,sm,_,_,_) -> sm
        | N -> failwith "N state in solution"

    let TurnOffSignal l d sm =
        match Map.tryFind (l,d) sm with
        | Some(_) -> Map.add (l,d) false sm
        | None -> sm

    let ChangeSignalMap s sm =
        match s with
        | S(h,_,tm,rm,p) -> S(h,sm,tm,rm,p)
        | _ -> failwith "N in ChangeSignalMap"

    let rec PathUntil l p = 
        match p with
        | [] -> []
        | x::xs when x = l -> [x]
        | x::xs -> x::(PathUntil l xs)

    let rec OffSignals sl p ep t d nsl = 
        match sl with
        | [] -> List.rev nsl
        | x::xs -> match p with
                   | [] -> failwith "Should not be here but OK"
                   | y::ys -> let l = GetTrainLocation x t
                              match l = y with
                              | true -> match ys with
                                        | [] -> List.rev (List.fold (fun s v -> v::s) nsl sl)
                                        | _ -> OffSignals xs p ep t d (x::nsl)
                              | false -> let sm = GetSignalMap x
                                         let ls = PathUntil y ep
                                         let nsm = List.fold (fun s v -> TurnOffSignal v d s) sm ls 
                                         let ns = ChangeSignalMap x nsm 
                                         OffSignals xs ys ep t d (ns::nsl)



    let TurnOffSignals sl t d = 
        //Find the path for the train
       
        let p = List.rev (List.fold (fun s v -> let l = GetTrainLocation v t
                                                match s with
                                                | [] -> [l]
                                                | x::xs when x = l -> s
                                                | x::xs -> l::s) [] sl)
        OffSignals sl p p t d []


    let CombineSolution sl ts =
        let slr = List.rev sl
        let r = List.rev (List.fold (fun s (t,d) -> TurnOffSignals s t d) slr ts)
        let a = 0
        r