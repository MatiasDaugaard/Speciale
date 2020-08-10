namespace Railways

open System.IO
open Railways.Types

//Module used to load a railway netork from a file

module LoadFiles = 

    // Function to translate string rail representation to rail
    let toRail (s:string) =
        let x = List.ofArray (s.Split ' ')
        (int(List.head x), int(List.item 1 x))

    // Function to translate string switchrail representation to switchrail
    let toSwitchRail (s:string) =
        let x = List.ofArray (s.Split ' ')
        let d = match List.item 3 x with
                | "L" -> L
                | "R" -> R
                | x -> failwith ("Direction illegal cannot translate " + x + " to a direction")
        (int(List.head x), int(List.item 1 x),int(List.item 2 x),d)

    // Function to translate string signal representation to signal
    let toSignal (s:string) = 
        let x = List.ofArray (s.Split ' ')
        let d = match List.item 1 x with
                | "L" -> L
                | "R" -> R
                | x -> failwith ("Direction illegal cannot translate " + x + " to a direction")
        (int(List.head x),d)

    // Function to translate string train representation to train
    let toTrain (s:string) = 
        let x = List.ofArray (s.Split ' ')
        let d = match List.item 3 x with
                | "L" -> L
                | "R" -> R
                | x -> failwith ("Direction illegal cannot translate " + x + " to a direction")
        ((List.head x), int(List.item 1 x),int(List.item 2 x),d)


    // Function used to load railway network from file in a given directory
    let LoadRailway f directoryPath : RailwayNetwork = 
        let path = Path.Combine(directoryPath,f)
        let lines = List.ofArray (File.ReadAllLines(path))
        // Load the locations
        let rec ExtractLocations l r =
            match l with
            | [] -> failwith "Ran out of lines when trying to read locations"
            | ":"::rest  -> r,rest
            | s::rest ->    ExtractLocations rest ((int (s))::r)

        let locations,rest = ExtractLocations lines []

        //Load the rails
        let rec ExtractRails l r =
            match l with
            | [] -> failwith "Ran out of lines when trying to read rails"
            | ":"::rest  -> r,rest
            | s::rest ->    ExtractRails rest ((toRail (s))::r)

        let rails,rest = ExtractRails rest []

        // Load the switchrails
        let rec ExtractSwitchRails l r =
            match l with
            | [] -> failwith "Ran out of lines when trying to read switch-rails"
            | ":"::rest  -> r,rest
            | s::rest ->    ExtractSwitchRails rest ((toSwitchRail (s))::r)

        let srails,rest = ExtractSwitchRails rest []

        //Load the signals
        let rec ExtractSignals l r =
            match l with
            | [] -> failwith "Ran out of lines when trying to read signals"
            | ":"::rest  -> r,rest
            | s::rest ->    ExtractSignals rest ((toSignal (s))::r)

        let sigs,rest = ExtractSignals rest []

        // Load the trains
        let rec ExtractTrains l r =
            match l with
            | [] -> r,[]
            | ":"::rest  -> r,rest
            | s::rest ->    ExtractTrains rest ((toTrain (s))::r)

        let trains,rest = ExtractTrains rest []

        locations,rails,srails,sigs,trains