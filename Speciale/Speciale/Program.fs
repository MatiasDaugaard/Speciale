open System
open Railways.Types
open Railways.BestFirst
open Railways.LoadFiles
open Railways.SaveFiles
open Railways.Preprocess
open System.IO


[<EntryPoint>]
let main args =
    printfn "Arguments passed to function : %A" args

    //cd Documents/Speciale/Speciale/Speciale/Speciale
    //fsharpc Types.fs Preprocessing.fs LoadFile.fs SaveFile.fs PriorityQueue.fs BFSSolver.fs Program.fs
    //mono Program.exe filename

    //TODO : Check if files exists
    let filename = match Array.tryHead args with
                   | Some(n) -> n
                   | None -> Console.WriteLine (sprintf "No filename entered")
                             "SWAP"

    

    let GameOver s =
        match s with
        | S(_,_,tm,_,_) -> let locs1 = valueSet tm
                           let locs2 = Set.ofSeq locs1
                           Seq.length locs1 <> Set.count locs2
        | _ -> failwith "GAMEOVER"  

    let rn = try 
                 LoadRailway (filename + ".txt")
             with
                 | _ -> ([],[],[],[],[])

    let stopWatch = System.Diagnostics.Stopwatch.StartNew()
    //Solve rn
    let result,gs = try
                        Solve rn
                    with
                    | _ -> ([],0)


    stopWatch.Stop()

    let time = stopWatch.Elapsed.TotalMilliseconds

    saveSolution result time gs filename

    List.iter (fun s -> if (GameOver s) then Console.WriteLine(sprintf "Something went wrong GameOver") else ()) (List.rev result)

    Console.WriteLine (sprintf "Time spend in total : %A (ms)" (time))
    Console.WriteLine(sprintf "Length of solution : %A" (List.length result))
    Console.WriteLine(sprintf "Generated states : %A" (gs))

    if gs = 0 then 1 else 0


