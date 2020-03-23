namespace Railways

open System.IO
open Railways.Types

module LoadFiles = 

    let toRail (s:string) =
        let x = List.ofArray (s.Split ' ')
        (int(List.head x), int(List.item 1 x))

    let toSplitRail (s:string) =
        let x = List.ofArray (s.Split ' ')
        let d = match List.item 3 x with
                | "L" -> L
                | "R" -> R
                | x -> failwith x
        (int(List.head x), int(List.item 1 x),int(List.item 2 x),d)

    let toSignal (s:string) = 
        let x = List.ofArray (s.Split ' ')
        let d = match List.item 1 x with
                | "L" -> L
                | "R" -> R
                | x -> failwith x
        (int(List.head x),d)

    let toTrain (s:string) = 
        let x = List.ofArray (s.Split ' ')
        let d = match List.item 3 x with
                | "L" -> L
                | "R" -> R
                | x -> failwith x
        ((List.head x), int(List.item 1 x),int(List.item 2 x),d)



    let LoadRailway f : RailwayNetwork = 

        let path = Path.Combine(__SOURCE_DIRECTORY__,f)
        let lines = List.ofArray (File.ReadAllLines(path))

        let rec ExtractLocations l r =
            match l with
            | [] -> failwith "F"
            | ":"::rest  -> r,rest
            | s::rest ->    ExtractLocations rest ((int (s))::r)

        let locations,rest = ExtractLocations lines []

        let rec ExtractRails l r =
            match l with
            | [] -> failwith "F"
            | ":"::rest  -> r,rest
            | s::rest ->    ExtractRails rest ((toRail (s))::r)

        let rails,rest = ExtractRails rest []

        let rec ExtractSplitRails l r =
            match l with
            | [] -> failwith "F"
            | ":"::rest  -> r,rest
            | s::rest ->    ExtractSplitRails rest ((toSplitRail (s))::r)

        let srails,rest = ExtractSplitRails rest []

        let rec ExtractSignals l r =
            match l with
            | [] -> failwith "F"
            | ":"::rest  -> r,rest
            | s::rest ->    ExtractSignals rest ((toSignal (s))::r)

        let sigs,rest = ExtractSignals rest []

        let rec ExtractTrains l r =
            match l with
            | [] -> failwith "F"
            | ":"::rest  -> r,rest
            | s::rest ->    ExtractTrains rest ((toTrain (s))::r)

        let trains,rest = ExtractTrains rest []

        locations,rails,srails,sigs,trains