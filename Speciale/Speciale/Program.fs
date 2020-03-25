open System
open FSharpx.Collections
open Railways.Types
open Railways.BestFirst
open Railways.LoadFiles



let GameOver s =
    match s with
    | S(_,_,tm,_,_,_) -> let locs1 = Map.values tm
                         let locs2 = Set.ofSeq locs1
                         Seq.length locs1 <> Set.count locs2
    | _ -> failwith "GAMEOVER"


let rn = LoadRailway "CopenhagenRealistic.txt"

let stopWatch = System.Diagnostics.Stopwatch.StartNew()
let result = (Solve rn)
stopWatch.Stop()

let PrintTrains s =
    match s with
    | S(_,_,tm,_,_,_) -> Console.WriteLine(sprintf "%A" (tm))
    | _ -> failwith "TRAINS"


Console.WriteLine (sprintf "Time spend in total : %A (ms)" (stopWatch.Elapsed.TotalMilliseconds))
List.iter (fun s -> if (GameOver s) then Console.WriteLine(sprintf "Something went wrong") else PrintTrains s) result
Console.WriteLine(sprintf "Length of solution : %A" (List.length result))


