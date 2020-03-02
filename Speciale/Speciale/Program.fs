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
    | S of int * SignalMap * TrainMap * SplitRailMap * State


//Static Information Variable Declaration
let mutable Trains:(Train*Direction) list = []
let mutable RWGRight:RailwayGraph = Map.empty
let mutable RWGLeft:RailwayGraph = Map.empty
let mutable Goal:(Train * Location) list = []

let mutable DistanceMapRight:Map<Location*Location,int> = Map.empty
let mutable DistanceMapLeft:Map<Location*Location,int> = Map.empty

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
    Goal <- List.rev (List.fold (fun s (t,_,l,_) -> (t,l)::s) [] tl)
    DistanceMapLeft <- CreateDistanceMap ll L
    DistanceMapRight <- CreateDistanceMap ll R
    S(0,sm,tm,rm,N)
    

// IsSolved checks if all trains are in their goal positions if so returns true
let IsSolved (s:State) = 
    match s with
    | N -> false
    | S(_,_,tm,_,_) -> List.forall (fun (t,l) -> Map.find t tm = l) Goal

// Creates the control program from a state by backtracking the states
// TODO : Should return a Map<Train*Location list, SignalMap*SplitRailMap
let rec ToControlProgram s = 
    match s with
    | N -> []
    | S(_,sm,tm,rm,x) -> (sm,tm,rm)::(ToControlProgram x)

// Checks if it is posible to move from l1 to l2 in current state
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


// Checks if any trains can currently reach each other returns true if not
let IsSafeState s = 
    match s with
    | S(_,sm,tm,rm,_) -> List.forall (fun (t,d) -> let rl = ReachableLocations t d sm tm rm
                                                   let tloc = Set.remove (Map.find t tm) (Set.ofSeq (Map.values tm))
                                                   Set.intersect rl tloc = Set.empty) Trains
    | _ -> failwith "Failed in IsSafeState function"  


//TODO : Should prob be a map
let rec GetGoal (t:Train) (tl)= 
    match tl with
    | [] -> failwith "Train does not have a goal, WHAT?!?!"
    | (n,g)::_ when n = t -> g
    | _::rs -> GetGoal t rs

// Calculates the total distance for the trains current position to their goal
let CalculateHeuristic (tm:TrainMap) = 
    List.fold (fun s (t,d) -> let l = Map.find t tm
                              let g = GetGoal t Goal
                              let dm = match d with
                                       | L -> DistanceMapLeft
                                       | R -> DistanceMapRight
                              s + Map.find (l,g) dm) 0 Trains

// Datastructure used to keep track of visited and non visited states
let mutable unexploredStatesPlayer:IPriorityQueue<State> = PriorityQueue.empty false
let mutable unexploredStatesConductor:IPriorityQueue<State> = PriorityQueue.empty false
let mutable exploredStates:Set<int> = Set.empty

// Add state to the queues
// Check if train has free route to other train if so do not add route
let AddNewState s t = 
    match s with
    | S(_,sm,tm,rm,_) -> match t with
                         | Conductor 
                         | Controller when (IsSafeState s) -> let h = hash(sm,tm,rm)
                                                              if not (Set.contains h exploredStates)
                                                              then unexploredStatesPlayer <- PriorityQueue.insert s unexploredStatesPlayer
                                                              unexploredStatesConductor <- PriorityQueue.insert s unexploredStatesConductor
                                                              exploredStates <- Set.add h exploredStates
                         | _ -> ()
                         //Console.WriteLine(sprintf "Explored states : %A" (Set.count exploredStates))
    | _ -> failwith "AddNewState"


// The game
let rec ControllerTurn n =
    match PriorityQueue.isEmpty unexploredStatesPlayer with
    | true when PriorityQueue.isEmpty unexploredStatesConductor -> failwith "No more states to explore"
    | true -> ConductorTurn n
    | _ -> let (s,p) = PriorityQueue.pop unexploredStatesPlayer
           unexploredStatesPlayer <- p
           match IsSolved s with
           | true  ->  List.rev (ToControlProgram s)
           | _ ->      match s with
                       | S(_,sm,tm,rm,_) -> Map.iter (fun k v -> let nSm = (Map.add k (not v) sm)
                                                                 let h = CalculateHeuristic  tm
                                                                 let nS = S(h,nSm,tm,rm,s)
                                                                 AddNewState nS Controller) sm
                                            Map.iter (fun k v -> let nRm = SwitchRail k rm
                                                                 let h = CalculateHeuristic tm
                                                                 let nS = S(h,sm,tm,nRm,s)
                                                                 AddNewState nS Controller) rm
                                            ConductorTurn n
                       | _ -> failwith "Not a state ControllerTurn function"

   and ConductorTurn n = 
    //Maybe not fail, but just next turn it
    match PriorityQueue.isEmpty unexploredStatesConductor with
    | true when PriorityQueue.isEmpty unexploredStatesPlayer -> failwith "No more states to explore"
    | true -> ControllerTurn n
    | _ -> let (s,p) = PriorityQueue.pop unexploredStatesConductor
           unexploredStatesConductor <- p
           match s with
           | S(_,sm,tm,rm,_) -> List.iter (fun (t,d) -> let l = Map.find t tm
                                                        List.iter (fun x -> let nTm = Map.add t x tm
                                                                            let h = CalculateHeuristic nTm
                                                                            let nS = S(h,sm,nTm,rm,s)
                                                                            AddNewState nS Conductor) (NextPosition l d sm rm)) Trains
                                ControllerTurn (n+1)
           | _ -> failwith "Not a state"


let rec Solve rn = 
    let s = InitiateState rn
    match IsSafeState s with
    | true -> unexploredStatesPlayer <- PriorityQueue.insert s unexploredStatesPlayer
              //priorityQueueConductor <- PriorityQueue.insert s priorityQueueConductor
              ControllerTurn 0
    | _ -> failwith "Initial state dangerous"



//type RailwayNetwork = Location list * Rail list * SplitRail list * Signal list * (Train*Location*Location*Direction) list

let locs = [1;2;3;4;5]
let rails = [(1,2);(2,3)]
let srails = [(3,4,5,R)]
let sigs = [(1,R)]
let trains = ["A",1,5,R]

let rn = (locs,rails,srails,sigs,trains):RailwayNetwork

let result = (Solve rn)
Console.WriteLine(sprintf "%A" (result))
Console.WriteLine(sprintf "Length of solution : %A" (List.length result))