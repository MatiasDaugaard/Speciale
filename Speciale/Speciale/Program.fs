open System
open Railways.Types
open Railways.LoadFiles
open Railways.Preprocess
open FSharpx.Collections


let rn = LoadRailway "Lyngby.txt"
let Trains, RWGLeft, RWGRight, Goal, DistanceMapLeft, DistanceMapRight, Paths, s = InitiateState rn

let hash (sm:SignalMap,tm:TrainMap,rm:SplitRailMap) = 
        Map.fold (fun s (a,b) v -> hash(s,a,b,v)) (Map.fold (fun s t l -> hash(s,t,l)) (Map.fold (fun s (l,d) b -> hash(s,l,d,b)) 0 sm) tm) rm



// IsSolved checks if all trains are in their goal positions if so returns true
let IsSolved (s:State) =  
    match s with
    | S(_,_,tm,_,_,_) -> Map.forall (fun t l -> Map.find t tm = l) Goal
    | _ -> failwith "IsSolved N"

// Checks if it is posible to move from l1 to l2 in current state/setup
let CanMove ((l1,l2):Rail) (d:Direction) (sm:SignalMap) (rm:SplitRailMap) =
    let l = l1
    let r = (l1,l2)
    let b1 = match Map.tryFind (l,d) sm with
             | None -> true
             | Some(x) -> x 
    let b2 = match Map.tryFind (r) rm with
             | None -> match Map.tryFind (l2,l1) rm with
                       | None -> true
                       | Some(x) -> x
             | Some(x) -> x
    b1 && b2   

// Finds all next possible locations from a given location and going in a given direction in the current state
let NextPosition (p:Location) (d:Direction) sm rm = 
    let x = match d with
            | L -> Map.find p RWGLeft
            | R -> Map.find p RWGRight
    List.fold (fun s v -> if CanMove (p,v) d sm rm then v::s else s) [] x

// Changes a splitrail from up to down and reversed
// TODO : Optimize, cause this is not a good way to do it (Change input of function to the actual split rail, currently not working if more than one switch rail is connected to a single location)
let SwitchRail ((rl1,rl2):Rail) (rm:Map<Rail,bool>) = 
    match Map.containsKey (rl1,rl2) rm with
    | true ->  Map.fold (fun s (l1,l2) v -> if l1 = rl1 
                                            then Map.add (l1,l2) (not v) s
                                            else s) rm rm
    | false -> Map.fold (fun s (l1,l2) v -> if l1 = rl2 
                                            then Map.add (l1,l2) (not v) s
                                            else s) rm rm

// Finds all currently reachable locations from a train
let ReachableLocations (t:Train) (d:Direction) (sm:SignalMap) (tm:TrainMap) (rm:SplitRailMap) = 
    let l = Map.find t tm
    let rec Locations (ls:Set<Location>) = 
        let nls = Set.fold (fun s p -> Set.union (List.fold (fun st va -> Set.add va st) Set.empty (NextPosition p d sm rm)) s) ls ls
        match ls = nls with
        | true -> ls
        | _ -> Locations nls
    Locations (Set.ofList (NextPosition l d sm rm))
    
    
// Checks if any trains can currently reach each other returns true if not or location not on path
let IsSafeState (s:State) =
    match s with
    | S(_,sm,tm,rm,ps,l) -> // Check if any train is near any of the changed location, if not state is not relevant
                            Map.exists (fun k v -> Set.contains v l && Map.find k Goal <> v) tm &&
                            // Checks if trains can reach other or can go off path, if true state is not relevant
                            List.forall (fun (t,d) -> let rl = ReachableLocations t d sm tm rm
                                                      let tloc = Set.remove (Map.find t tm) (Set.ofSeq (Map.values tm))
                                                      //Should not be able to reach another train
                                                      Set.intersect rl tloc = Set.empty &&
                                                      // Should not be able to reach location not on path
                                                      Set.difference rl (Map.find t Paths) = Set.empty) Trains
    | _ -> failwith "IsSafeState N"


//Calculates total distance for the trains current position to their goal, 
//TODO : Make smarter
let CalculateHeuristic (tm:TrainMap) = 
    List.fold (fun s (t,d) -> let l = Map.find t tm
                              let g = Map.find t Goal
                              if l = g then s else
                              let dm = match d with
                                       | L -> DistanceMapLeft
                                       | R -> DistanceMapRight
                              s + Map.find (l,g) dm
                              ) 0 Trains
                              

// Datastructure used to keep track of visited and non visited states
let mutable unexploredStatesPlayer:IPriorityQueue<State> = PriorityQueue.empty false
let mutable unexploredStatesConductor:IPriorityQueue<State> = PriorityQueue.empty false
let mutable generatedStates:Set<StateID> = Set.empty

// Add state to the queues
let AddState s h = 
    if not (Set.contains h generatedStates)
    then unexploredStatesPlayer <- PriorityQueue.insert s unexploredStatesPlayer
         unexploredStatesConductor <- PriorityQueue.insert s unexploredStatesConductor
         generatedStates <- Set.add h generatedStates
    else ()

let AddNewState (s:State) t = 
    let x = match s with
            | S(_,sm,tm,rm,_,_) -> (sm,tm,rm)
            | _ -> failwith "Add new state N"
    let h = hash x
    match t with
    | Conductor -> AddState s h                   
    | Controller when (IsSafeState s) -> AddState s h
    | _ -> ()


// Creates the control program from a state by backtracking the states
// TODO : Should return a Map<Train*Location list, SignalMap*SplitRailMap
let rec ToControlProgram s = 
    match s with
    |S(_,sm,tm,rm,x,_) when x <> N -> s::ToControlProgram x
    | _ -> [s]

// The game
let rec ControllerTurn _ =
    match PriorityQueue.isEmpty unexploredStatesPlayer with
    | true when PriorityQueue.isEmpty unexploredStatesConductor -> failwith "No more states to explore"
    | true -> ConductorTurn 0
    | _ -> let (s,p) = PriorityQueue.pop unexploredStatesPlayer
           unexploredStatesPlayer <- p
           match IsSolved s with
           | true  ->  List.rev (ToControlProgram s)
           | _ ->      match s with
                       | S(_,sm,tm,rm,_,_) -> let sm = Map.fold (fun s k v -> Map.add k false s) Map.empty sm
                                              Map.iter (fun k v -> let nSm = (Map.add k (not v) sm)
                                                                   let h = CalculateHeuristic tm
                                                                   let nS = S(h+1,nSm,tm,rm,s,set[fst k])
                                                                   AddNewState nS Controller) sm
                                              Map.iter (fun k v -> let nRm = SwitchRail k rm
                                                                   let h = CalculateHeuristic tm
                                                                   let nS = S(h+1,sm,tm,nRm,s,set [fst k; snd k])
                                                                   AddNewState nS Controller) rm
                                              ConductorTurn 0
                       | _ -> failwith "ControllerTurn"

   and ConductorTurn _ = 
    match PriorityQueue.isEmpty unexploredStatesConductor with
    | true when PriorityQueue.isEmpty unexploredStatesPlayer -> failwith "No more states to explore"
    | true -> ControllerTurn 0
    | _ -> let (s,p) = PriorityQueue.pop unexploredStatesConductor
           unexploredStatesConductor <- p
           match s with
           | S(_,sm,tm,rm,_,_) -> List.iter (fun (t,d) -> let l = Map.find t tm
                                                          List.iter (fun x -> let nTm = Map.add t x tm
                                                                              let h = CalculateHeuristic nTm
                                                                              let nS = S(h,sm,nTm,rm,s,Set.empty)
                                                                              AddNewState nS Conductor)  (NextPosition l d sm rm)) Trains
                                  ControllerTurn 0
           | _ -> failwith "ConductorTurn" 




let rec Solve s = 
    unexploredStatesPlayer <- PriorityQueue.insert s unexploredStatesPlayer
    ControllerTurn 0

      

    







let stopWatch = System.Diagnostics.Stopwatch.StartNew()
let result = (Solve s)
stopWatch.Stop()
Console.WriteLine (sprintf "Time spend in total : %A (ms)" (stopWatch.Elapsed.TotalMilliseconds))
//List.iter (fun (S(_,_,x,_,_,_)) -> Console.WriteLine(sprintf "%A" (x))) result
//Console.WriteLine(sprintf "%A" (result))
Console.WriteLine(sprintf "Length of solution : %A" (List.length result))

Console.WriteLine(sprintf "Explored states : %A" (Set.count generatedStates))



