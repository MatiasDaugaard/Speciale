namespace Railways



open System
open Railways.Types
open Railways.LoadFiles
open Railways.Preprocess
open FSharpx.Collections

module BestFirst =

    let Solve rn = 

        let Trains, RWGLeft, RWGRight, Goal, DistanceMapLeft, DistanceMapRight, Paths, SwitchRails, Priorities, s = InitiateState rn

        let hash s = 
            match s with
            | S(_,sm,tm,rm,_,_) -> Map.fold (fun s (a,b,c,d) v -> hash(s,a,b,c,d,v)) (Map.fold (fun s t l -> hash(s,t,l)) (Map.fold (fun s (l,d) b -> hash(s,l,d,b)) 0 sm) tm) rm
            | _ -> failwith "Cannot hash N"    

        // IsSolved checks if all trains are in their goal positions if so returns true
        let IsSolved (s:State) =  
            match s with
            | S(_,_,tm,_,_,_) -> Map.forall (fun t l -> Map.find t tm = l) Goal
            | _ -> failwith "IsSolved N"

        // Checks if it is posible to move from l1 to l2 in current state/setup
        let CanMove ((l1,l2):Rail) (d:Direction) (sm:SignalMap) (rm:SwitchRailMap) =
            let l = l1
            let r = (l1,l2)
            let b1 = match Map.tryFind (l,d) sm with
                     | None -> true
                     | Some(x) -> x 
            let b2 = match Map.tryFind (r) SwitchRails with
                     | None -> true
                     | Some(x) -> let (_,lx,_,_) = x
                                  let b = Map.find x rm
                                  if lx = l1 || lx = l2 then b else not b
                                  
            b1 && b2   

        // Finds all next possible locations from a given location and going in a given direction in the current state
        let NextPosition (p:Location) (d:Direction) sm rm = 
            let x = match d with
                    | L -> Map.find p RWGLeft
                    | R -> Map.find p RWGRight
            List.fold (fun s v -> if CanMove (p,v) d sm rm then v::s else s) [] x

        // Changes a splitrail from up to down and reversed
        let SwitchRail (sr:SwitchRail) (rm:SwitchRailMap) = 
            let b = Map.find sr rm
            Map.add sr (not b) rm

        // Get the locations for a given switchrail
        let getSwitchRailLocation ((l1,l2,l3,_):SwitchRail) = set [l1;l2;l3]

        // Finds all currently reachable locations from a train
        let ReachableLocations (t:Train) (d:Direction) (sm:SignalMap) (tm:TrainMap) (rm:SwitchRailMap) = 
            let l = Map.find t tm
            let rec Locations (ls:Set<Location>) = 
                let nls = Set.fold (fun s p -> Set.union (List.fold (fun st va -> Set.add va st) Set.empty (NextPosition p d sm rm)) s) ls ls
                match ls = nls with
                | true -> ls
                | _ -> Locations nls
            Locations (Set.ofList (NextPosition l d sm rm))


        // Checks if the state is smart, that the last change is relevant, for example signal turned on is near train, returns true if the case.
        let IsSmartState (s:State) = 
            match s with
            | S(_,sm,tm,rm,ps,l) -> // Check if any train is near any of the changed location, if not state is not relevant
                                    Map.exists (fun k v -> Set.contains v l && Map.find k Goal <> v) tm 
            | _ -> failwith "IsSmartState N"


        // Checks if any trains can currently reach another train returns true if not or reachable location not on path
        let IsSafeState (s:State) =
            match s with
            | S(_,sm,tm,rm,ps,l) -> // Checks if trains can reach other or can go off path, if true state is not relevant
                                    List.forall (fun (t,d) -> let rl = ReachableLocations t d sm tm rm
                                                              let tloc = Set.remove (Map.find t tm) (Set.ofSeq (Map.values tm))
                                                              //Should not be able to reach another train
                                                              Set.intersect rl tloc = Set.empty &&
                                                              // Should not be able to reach location not on path
                                                              Set.difference rl (Map.find t Paths) = Set.empty) Trains
            | _ -> failwith "IsSafeState N"


        //Calculates total distance for the trains current position to their goal, 
        //TODO : Make smarter , the random number should be some sort of priority
        let CalculateHeuristic (tm:TrainMap) (ls:Set<Location>) = 
            List.fold (fun s (t,d) -> let l = Map.find t tm
                                      let g = Map.find t Goal
                                      if l = g then s else
                                      let dm = match d with
                                               | L -> DistanceMapLeft
                                               | R -> DistanceMapRight
                                      s + ((Map.find t Priorities) * (Map.find (l,g) dm))
                                      - (Map.find t Priorities) * (Set.count (Set.intersect ls (set[l])))
                                      ) 0 Trains
                                      

        // Datastructure used to keep track of visited and non visited states
        let mutable unexploredStatesController:IPriorityQueue<State> = PriorityQueue.empty false
        let mutable generatedStates:Set<StateID> = Set.empty

        // Add state to the queues
        let AddState s h = 
            if not (Set.contains h generatedStates)
            then unexploredStatesController <- PriorityQueue.insert s unexploredStatesController
                 generatedStates <- Set.add h generatedStates
                 true
            else false

        let AddNewState (s:State) t = 
            let h = hash s
            match t with
            | Conductor -> AddState s h                   
            | Controller when (IsSmartState s) && (IsSafeState s)  -> AddState s h
            | _ -> false


        // Creates the control program from a state by backtracking the states
        // TODO : Should return a Map<Train*Location list, SignalMap*SwitchRailMap>
        let rec ToControlProgram s = 
            match s with
            |S(_,sm,tm,rm,x,_) when x <> N -> s::ToControlProgram x
            | _ -> [s]


        //Function for finding all new states by moving trains in given state
        let GenerateConductorStates s = 
            match s with
            | S(_,sm,tm,rm,_,_) -> List.fold (fun q (t,d) -> let l = Map.find t tm
                                                             let ss = List.fold (fun z x -> let nTm = Map.add t x tm
                                                                                            let h = CalculateHeuristic nTm Set.empty
                                                                                            let nS = S(h,sm,nTm,rm,s,Set.empty)
                                                                                            if AddNewState nS Conductor then Set.add nS z else z) Set.empty (NextPosition l d sm rm)
                                                             ss + q) Set.empty Trains
            | _ -> failwith "ConductorTurn"

        // The game
        let rec ControllerTurn _ =
            match PriorityQueue.isEmpty unexploredStatesController with
            | true -> failwith "No more states to explore"
            | _ -> let (s,p) = PriorityQueue.pop unexploredStatesController
                   unexploredStatesController <- p
                   match IsSolved s with
                   | true  ->  List.rev (ToControlProgram s)
                   | _ ->      match s with
                               | S(x,sm,tm,rm,_,_) ->  let smn = Map.fold (fun s k v -> Map.add k false s) Map.empty sm
                                                       let s1 = Map.fold (fun sx k v -> let nSm = (Map.add k (not v) smn)
                                                                                        let h = CalculateHeuristic tm (set[fst k])
                                                                                        let nS = S(h,nSm,tm,rm,s,set[fst k])
                                                                                        if AddNewState nS Controller then Set.add nS sx else sx) Set.empty sm
                                                       let s2 = Map.fold (fun sx k v -> let nRm = SwitchRail k rm
                                                                                        let h = CalculateHeuristic tm (getSwitchRailLocation k)
                                                                                        let nS = S(h,sm,tm,nRm,s,(getSwitchRailLocation k))
                                                                                        if AddNewState nS Controller then Set.add nS sx else sx) Set.empty rm

                                                       ConductorTurn (s1 + s2)
                                            | _ -> failwith "ControllerTurn"

           and ConductorTurn (states:Set<State>) = 
            match Set.isEmpty states with
            | true when PriorityQueue.isEmpty unexploredStatesController -> failwith "No more states to explore"
            | true -> ControllerTurn 0
            | _ -> let nStates = Set.fold (fun s v -> s + GenerateConductorStates v) Set.empty states
                   ConductorTurn nStates
                   
                    

        

        unexploredStatesController <- PriorityQueue.insert s unexploredStatesController
        ControllerTurn 0

