open System
open FSharpx.Collections



// Type declarations
type Train = string
type Direction = L | R
type Location = int
type Rail = Location * Location
type SplitRail = Location * Location * Location * Direction
type Turn = Controller | Conductor
type Signal = Location * Direction


// List of Location (Nodes), Rails (Vertex), SplitRail (Vertex), Signal (Signals), T*L*L*D (Train,Start,End,Direction)
type RailwayNetwork = Location list * Rail list * SplitRail list * Signal list * (Train*Location*Location*Direction) list
type RailwayGraph = Map<Location, Location list>

type SignalMap = Map<Signal, bool>
type TrainMap = Map<Train,Location>
type SplitRailMap = Map<Rail,bool>


type State =
    | N 
    | S of int * SignalMap * TrainMap * SplitRailMap * State * Set<Location>


// Static Information Variable Declaration
let mutable Trains:(Train*Direction) list = []
let mutable RWGRight:RailwayGraph = Map.empty
let mutable RWGLeft:RailwayGraph = Map.empty
let mutable Goal:Map<Train,Location> = Map.empty

let mutable Paths:(Map<Train,Set<Location>>) = Map.empty

let mutable DistanceMapRight:Map<Location*Location,int> = Map.empty
let mutable DistanceMapLeft:Map<Location*Location,int> = Map.empty


// PREPROCCESSING PART

// Used for creating the railway graph
let addVertex ((l1,l2):Rail) (m:RailwayGraph) = 
    let ll = Map.find l1 m
    Map.add l1 (l2::ll) m


// Distance from Location l in direction d to all other reachable locations
let rec CreateDistanceMapLoc (loc:Location) (d:Direction) (currentLocations:Set<Location>) (explored:Set<Location>) c m =
    let rwg = match d with
              | L -> RWGLeft
              | R -> RWGRight
    match Set.isEmpty currentLocations with
    | true -> m
    | _ -> let nexts = Set.difference (Set.fold (fun s v -> Set.ofList (Map.find v rwg) + s) Set.empty currentLocations) explored
           let nm = Set.fold (fun s v -> Map.add (loc,v) c s) m nexts
           CreateDistanceMapLoc loc d nexts (Set.union nexts explored) (c+1) nm


let CreateDistanceMap ll d = List.fold (fun s v -> CreateDistanceMapLoc v d (set [v]) (set [v]) 1 (Map.add (v,v) 0 s)) Map.empty ll

let FindPaths (tl:(Train*Location) list) =
    let rec Path d s =
        let rwg = match d with
                  | L -> RWGLeft
                  | _ -> RWGRight
        let x = Set.fold (fun st v -> Set.union (Set.ofList (Map.find v rwg)) st) s s
        match x = s with
        | true -> x
        | _ -> Path d x

    Paths <- List.fold (fun s (t,d) -> let sl = snd (List.find (fun (x,_) -> x = t) tl)
                                       let gl = Map.find t Goal
                                       let paths1 = Path d (set [sl])
                                       let a = if d = L then R else L
                                       let paths2 = Path a (set [gl])
                                       let paths = Set.intersect paths1 paths2
                                       Map.add t paths s) Map.empty Trains





// InitiateState creates the initial state given a railway network, and sets static variables
// Type : RailwayNetwork -> State
let InitiateState (ll,rl,srl,sl,tl) = 

    let sm = List.fold (fun s v -> Map.add v false s) Map.empty sl
    let tm = List.fold (fun s (t,l,_,_) -> Map.add t l s) Map.empty tl
    let rm = List.fold (fun s (l1,l2,l3,d) -> (Map.add (l1,l2) true) (Map.add (l1,l3) false s)) Map.empty srl
    let rwg = List.fold (fun s l -> Map.add l [] s) Map.empty ll

    let rwgRight1 = List.fold (fun s r -> addVertex r s) rwg rl
    let rwgRight2 = List.fold (fun s (l1,l2,l3,d) -> if d = R then addVertex (l1,l2) (addVertex (l1,l3) s) else addVertex (l2,l1) (addVertex (l3,l1) s)) rwgRight1 srl

    let rwgLeft1 = List.fold (fun s (l1,l2) -> addVertex (l2,l1) s) rwg rl
    let rwgLeft2 = List.fold (fun s (l1,l2,l3,d) -> if d = L then addVertex (l1,l2) (addVertex (l1,l3) s) else addVertex (l2,l1) (addVertex (l3,l1) s)) rwgLeft1 srl

    Trains <- List.rev (List.fold (fun s (t,_,_,d) -> (t,d)::s) [] tl)
    RWGRight <- rwgRight2
    RWGLeft <- rwgLeft2
    Goal <- (List.fold (fun s (t,_,l,_) -> Map.add t l s) Map.empty tl)
    DistanceMapLeft <- CreateDistanceMap ll L
    DistanceMapRight <- CreateDistanceMap ll R
    FindPaths (Map.toList tm)
    S(0,sm,tm,rm,N,Set.empty)
    

// IsSolved checks if all trains are in their goal positions if so returns true
let IsSolved (s:State) = 
    match s with
    | N -> false
    | S(_,_,tm,_,_,_) -> Map.forall (fun t l -> Map.find t tm = l) Goal

// Creates the control program from a state by backtracking the states
// TODO : Should return a Map<Train*Location list, SignalMap*SplitRailMap
let rec ToControlProgram s = 
    match s with
    | N -> []
    | S(_,sm,tm,rm,x,_) -> (sm,tm,rm)::(ToControlProgram x)

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
// TODO : Optimize, cause this is not a good way to do it (Change input of function to the actual split rail)
let SwitchRail ((rl1,rl2):Rail) (rm:Map<Rail,bool>) = 
    match Map.containsKey (rl1,rl2) rm with
    | true ->  Map.fold (fun s (l1,l2) v -> if l1 = rl1 
                                            then Map.add (l1,l2) (not v) s
                                            else s) rm rm
    | false -> Map.fold (fun s (l1,l2) v -> if l1 = rl2 
                                            then Map.add (l1,l2) (not v) s
                                            else s) rm rm

//Finds all currently reachable locations from a train
let ReachableLocations (t:Train) (d:Direction) (sm:SignalMap) (tm:TrainMap) (rm:SplitRailMap) = 
    let l = Map.find t tm
    let rec Locations (ls:Set<Location>) = 
        let nls = Set.fold (fun s p -> Set.union (List.fold (fun st va -> Set.add va st) Set.empty (NextPosition p d sm rm)) s) ls ls
        match ls = nls with
        | true -> ls
        | _ -> Locations nls
    Locations (Set.ofList (NextPosition l d sm rm))
    
    
// Checks if any trains can currently reach each other returns true if not or location not on path
let IsSafeState s = 
    match s with                    
    | S(_,sm,tm,rm,ps,l) -> // Check if any train is near any of the changed location, if not state is not relevant
                            Map.exists (fun k v -> Set.contains v l) tm &&
                            // Checks if trains can reach other or can go off path, if true state is not relevant
                            List.forall (fun (t,d) -> let rl = ReachableLocations t d sm tm rm
                                                      let tloc = Set.remove (Map.find t tm) (Set.ofSeq (Map.values tm))
                                                      //Should not be able to reach another train
                                                      Set.intersect rl tloc = Set.empty &&
                                                      // Should not be able to reach location not on path
                                                      Set.difference rl (Map.find t Paths) = Set.empty) Trains
    | _ -> failwith "Failed in IsSafeState function"  

//Calculates total distance for the trains current position to their goal, TODO : Make smarter
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
let mutable generatedStates:Set<int> = Set.empty

// Add state to the queues
let AddState s h = 
    if not (Set.contains h generatedStates)
    then unexploredStatesPlayer <- PriorityQueue.insert s unexploredStatesPlayer
    unexploredStatesConductor <- PriorityQueue.insert s unexploredStatesConductor
    generatedStates <- Set.add h generatedStates



let AddNewState s t = 
    match s with
    | S(_,sm,tm,rm,_,_) -> let h = hash(sm,tm,rm)
                           match t with
                           | Conductor -> AddState s h                   
                           | Controller when (IsSafeState s) -> AddState s h
                           | _ -> ()


    | _ -> failwith "AddNewState"


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
                       | S(_,sm,tm,rm,_,_) -> Map.iter (fun k v -> let nSm = (Map.add k (not v) sm)
                                                                   let h = CalculateHeuristic tm
                                                                   let nS = S(h,nSm,tm,rm,s,set[fst k])
                                                                   AddNewState nS Controller) sm
                                              Map.iter (fun k v -> let nRm = SwitchRail k rm
                                                                   let h = CalculateHeuristic tm
                                                                   let nS = S(h,sm,tm,nRm,s,set [fst k; snd k])
                                                                   AddNewState nS Controller) rm
                                              ConductorTurn 0
                       | _ -> failwith "Not a state ControllerTurn function"

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
                                                                              AddNewState nS Conductor) (NextPosition l d sm rm)) Trains
                                  ControllerTurn 0
           | _ -> failwith "Not a state"


let rec Solve rn = 
    let stopWatch = System.Diagnostics.Stopwatch.StartNew()
    let s = InitiateState rn
    stopWatch.Stop()
    Console.WriteLine (sprintf "Time spend preprocessing: %A (ms)" (stopWatch.Elapsed.TotalMilliseconds))

    unexploredStatesPlayer <- PriorityQueue.insert s unexploredStatesPlayer
    //unexploredStatesConductor <- PriorityQueue.insert s unexploredStatesConductor
    ControllerTurn 0




//type RailwayNetwork = Location list * Rail list * SplitRail list * Signal list * (Train*Location*Location*Direction) list
(*
//Simple test
let locs = [1;2;3;4;5;6]
let rails = [(1,2);(5,6)]
let srails = [(2,3,4,R);(5,3,4,L)]
let sigs = [(1,R);(6,L)]
let trains = [("A",1,6,R);("B",6,1,L)]
*)
(*
//Lyngby
let locs = [1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22]
let rails = [(1,2);(3,4);(5,6);(7,8);(9,10);(11,12);(13,14);(15,16);(17,18);(19,20);(21,22)]
let srails = [(2,3,9,R);(5,4,8,L);(11,10,16,L);(12,7,13,R);(18,15,19,R);(21,14,20,L)]
let sigs = [(1,L);(2,R);(3,L);(4,R);(5,L);(6,R);(11,L);(12,R);(17,L);(18,R);(19,L);(20,R);(21,L);(22,R)]
let trains = [("t4",1,6,R);("t5",6,1,L);("t1",17,22,R);("t3",19,17,L);("t2",22,19,L)]
*)


//Toy
let locs = [1;2;3]
let rails = []
let srails = [(3,1,2,L)]
let sigs = [(1,R)]
let trains = [("t1",1,3,R);("t2",3,2,L)]

let rn = (locs,rails,srails,sigs,trains):RailwayNetwork

let stopWatch = System.Diagnostics.Stopwatch.StartNew()
let result = (Solve rn)
stopWatch.Stop()
Console.WriteLine (sprintf "Time spend in total : %A (ms)" (stopWatch.Elapsed.TotalMilliseconds))

//Console.WriteLine(sprintf "%A" (result))
Console.WriteLine(sprintf "Length of solution : %A" (List.length result))

Console.WriteLine(sprintf "Explored states : %A" (Set.count generatedStates))
