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
    
    let filename = match Array.tryHead args with
                   | Some(n) -> n
                   | None -> Console.WriteLine (sprintf "No filename entered")
                             "SWAP"

    let path = match Array.tryItem 1 args with
                   | Some(n) -> n
                   | None -> Console.WriteLine (sprintf "No directory entered")
                             __SOURCE_DIRECTORY__

    let GameOver s =
        match s with
        | S(_,_,tm,_,_) -> let locs1 = valueSet tm
                           let locs2 = Set.ofSeq locs1
                           Seq.length locs1 <> Set.count locs2
        | _ -> failwith "GAMEOVER"  

    let rn = try 
                 LoadRailway (filename + ".txt") path
             with
                 | _ -> ([],[],[],[],[])

                 
    let result,gs,pretime,solvetime,posttime = try
                                                   Solve rn
                                               with
                                               | _ -> ([],0,0.0,0.,0.0)
                                      
    
                             
    saveSolution result (pretime+solvetime+posttime) gs filename path

    List.iter (fun s -> if (GameOver s) then Console.WriteLine(sprintf "Something went wrong GameOver") else ()) (List.rev result)

    Console.WriteLine (sprintf "Time spend in preprocess : %A (ms)" (pretime))
    Console.WriteLine (sprintf "Time spend in solving : %A (ms)" (solvetime))
    Console.WriteLine (sprintf "Time spend in postprocess : %A (ms)" (posttime))
    Console.WriteLine(sprintf "Length of solution : %A" (List.length result))
    Console.WriteLine(sprintf "Generated states : %A" (gs))

    if gs = 0 then 1 else 0


