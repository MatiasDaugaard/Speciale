﻿open System
open FSharpx.Collections
open Railways.Types
open Railways.BestFirst
open Railways.LoadFiles
open System.IO




let GameOver s =
    match s with
    | S(_,_,tm,_,_) -> let locs1 = Map.values tm
                       let locs2 = Set.ofSeq locs1
                       Seq.length locs1 <> Set.count locs2
    | _ -> failwith "GAMEOVER"


let filename = "CopenhagenAgain"

let rn = LoadRailway (filename + ".txt")

let stopWatch = System.Diagnostics.Stopwatch.StartNew()
let result,x = (Solve rn)
stopWatch.Stop()

let PrintTrains s =
    match s with
    | S(_,_,tm,_,_) -> Console.WriteLine(sprintf "%A" (tm))
    | _ -> failwith "TRAINS"


Console.WriteLine (sprintf "Time spend in total : %A (ms)" (stopWatch.Elapsed.TotalMilliseconds))
List.iter (fun s -> if (GameOver s) then Console.WriteLine(sprintf "Something went wrong GameOver") else ()) (List.rev result)


let solutionSequence (sol:State list) =
        let template = "<trains>{0}\n<signals>{1}\n<rails>{2}"


        let locs m = let s = seq{
                                  for x in Map.values m do
                                      yield (string x)
                              }
                     String.concat ";" (s)
        let bLocs m = let s = seq{
                                  for x in Map.values m do
                                      yield if x then "T" else "F" 
                              }
                      String.concat ";" ( s)

        let row (s) =
            match s with
            | S(_,sm,tm,rm,_) -> sprintf "<>\n<trains>[%s]\n<signals>[%s]\n<rails>[%s]\n</>"  (locs tm) (bLocs sm) (bLocs rm)
            | _ -> failwith "F"

        seq {
            yield "<solution>"
            for x in sol  do
                yield row x
            yield "</solution>"
        }


let path = Path.Combine(__SOURCE_DIRECTORY__,(filename + ".sol"))
File.WriteAllLines (path, solutionSequence (List.rev result)) |> ignore

Console.WriteLine(sprintf "Length of solution : %A" (List.length result))
Console.WriteLine(sprintf "Generated states : %A" (x))


