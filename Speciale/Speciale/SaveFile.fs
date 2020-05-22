namespace Railways

open System.IO
open Railways.Types
open FSharpx.Collections

module SaveFiles = 

    let saveSolution sol t gs fn = 

        let solutionSequence (sol:State list) =
                let template = "<trains>{0}\n<signals>{1}\n<rails>{2}"


                let locs m = 
                    let s = seq{
                                for x in Map.values m do
                                    yield (string x)
                            }
                    String.concat ";" (s)
                let bLocs m = 
                    let s = seq{
                        for x in Map.values m do
                            yield if x then "T" else "F" 
                            }
                    String.concat ";" ( s)

                let stateSeq (s) =
                    match s with
                    | S(_,sm,tm,rm,_) -> sprintf "<>\n<trains>[%s]\n<signals>[%s]\n<rails>[%s]\n</>"  (locs tm) (bLocs sm) (bLocs rm)
                    | _ -> failwith "F"

                seq {
                    yield "<solution>"
                    for x in sol  do
                        yield stateSeq x
                    yield (sprintf "<states> %A" (List.length sol))
                    yield (sprintf "<generated> %A" gs)
                    yield (sprintf "<time> %A" (t))
                    yield "</solution>"
                }


        let path = Path.Combine(__SOURCE_DIRECTORY__,(fn + ".sol"))

        File.WriteAllLines (path, solutionSequence (List.rev sol)) |> ignore