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


let rn = LoadRailway "Lyngby.txt"

let stopWatch = System.Diagnostics.Stopwatch.StartNew()
let result = (Solve rn)
stopWatch.Stop()



Console.WriteLine (sprintf "Time spend in total : %A (ms)" (stopWatch.Elapsed.TotalMilliseconds))
List.iter (fun s -> if (GameOver s) then Console.WriteLine(sprintf "Something went wrong") else ()) result
Console.WriteLine(sprintf "Length of solution : %A" (List.length result))


