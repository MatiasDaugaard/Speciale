﻿namespace Railways

open System.IO
open System
open Railways.Types

//Module used to save a solution to a file

module SaveFiles = 

    let saveSolution sol t gs fn directoryPath = 

        let mapValues m = 
            let l = Map.fold (fun s k v -> v::s) [] m
            seq{
                for x in List.rev l do
                    yield x
            }
            


        let solutionSequence (sol:State list) =
    
                let locs m = 
                    let s = seq{
                                for x in mapValues m do
                                    yield (string x)
                            }
                    String.concat ";" (s)
                let bLocs m = 
                    let s = seq{
                        for x in mapValues m do
                            yield if x then "T" else "F" 
                            }
                    String.concat ";" ( s)

                let stateSeq (s) =
                    match s with
                    | S(_,sm,tm,rm,_) -> sprintf "<>\n<trains>[%s]\n<signals>[%s]\n<rails>[%s]\n</>"  (locs tm) (bLocs sm) (bLocs rm)
                    | _ -> failwith "N state in solution"

                seq {
                    yield "<solution>"
                    for x in sol  do
                        yield stateSeq x
                    yield (sprintf "<states> %A" (List.length sol))
                    yield (sprintf "<generated> %A" gs)
                    yield (sprintf "<time> %A" (t))
                    yield "</solution>"
                }


        let path = Path.Combine(directoryPath,(fn + ".sol"))

        File.WriteAllLines (path, solutionSequence (List.rev sol)) |> ignore