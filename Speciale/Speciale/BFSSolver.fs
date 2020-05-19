namespace Railways

open System
open Railways.Types
open Railways.Preprocess
open FSharpx.Collections

module BestFirst =

    let Solve rn = 

        let Trains, RWGLeft, RWGRight, Goal, DistanceMapLeft, DistanceMapRight, Paths, SwitchRails, Priorities, MaxPrio, SM, s = InitiateState rn

        // Function for hashing a state
        let hash s = 
            match s with
            | S(_,sm,tm,rm,_) -> Map.fold (fun s (a,b,c,d) v -> hash(s,a,b,c,d,v)) (Map.fold (fun s t l -> hash(s,t,l)) (Map.fold (fun s (l,d) b -> hash(s,l,d,b)) 0 sm) tm) rm
            | _ -> failwith "Cannot hash N"    

        // Checks if all trains are in their goal positions if so returns true
        let IsSolved (s:State) =  
            match s with
            | S(_,_,tm,_,_) -> Map.forall (fun t l -> Map.find t tm = l) Goal
            | _ -> failwith "IsSolved N"

        // Checks if it is posible to move from l1 to l2 in current state
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

        // Changes a switchrail from up to down and reversed
        let SwitchRail (sr:SwitchRail) (rm:SwitchRailMap) = 
            let b = Map.find sr rm
            Map.add sr (not b) rm

        // Get the locations assosiated for a given switchrail status
        let getSwitchRailLocation ((l1,l2,l3,d):SwitchRail) rm = if Map.find (l1,l2,l3,d) rm then set [l1;l2] else set [l1;l3]

        // Finds all currently reachable locations from a train
        let ReachableLocations (t:Train) (d:Direction) (sm:SignalMap) (tm:TrainMap) (rm:SwitchRailMap) = 
            let l = Map.find t tm
            let rec Locations (ls:Set<Location>) = 
                let nls = Set.fold (fun s p -> let y = (NextPosition p d sm rm)
                                               let x = (List.fold (fun st va -> Set.add va st) Set.empty y)
                                               Set.union x s) ls ls
                match ls = nls with
                | true -> ls
                | _ -> Locations nls
            Locations (Set.ofList (NextPosition l d sm rm))


        // Checks if the state is smart, that the last change is relevant, for example signal turned on is near train, returns true if the case.
        let IsSmartState (s:State) l = 
            match s with
            | S(_,_,tm,_,_) -> // Check if any train is near any of the changed location, if not state is not relevant
                               Map.exists (fun k v -> Set.contains v l && Map.find k Goal <> v) tm 
            | _ -> failwith "IsSmartState N"


        // Checks if any trains can currently reach another train returns true if not or reachable location not on path
        let IsSafeState (s:State) =
            match s with
            | S(_,sm,tm,rm,_) -> // Checks if trains can reach other or can go off path, if true state is not safe
                                 // TODO : Check if train can reach other trains reachable locations aswell
                                 let arl = List.fold (fun s (t,d) -> Map.add t (ReachableLocations t d sm tm rm) s) Map.empty Trains
                                 List.forall (fun (t,d) -> let rl = Map.find t arl
                                                           let rls = Map.fold (fun s k v -> if k = t 
                                                                                            then 
                                                                                                s
                                                                                            else 
                                                                                                Set.union s v) Set.empty arl
                                                              //Should not be able to reach another train
                                                           let tloc = Set.remove (Map.find t tm) (Set.ofSeq (Map.values tm))
                                                           let locs = Set.union rls tloc
                                                           Set.intersect rl locs = Set.empty &&
                                                              // Should not be able to reach location not on path
                                                           Set.difference rl (Map.find t Paths) = Set.empty) Trains
            | _ -> failwith "IsSafeState N"


        //Calculates total distance for the trains current position to their goal times the priority of the train
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

        // Add state to the queues if it has not been added before
        let AddState s h = 
            if not (Set.contains h generatedStates)
            then unexploredStatesController <- PriorityQueue.insert s unexploredStatesController
                 generatedStates <- Set.add h generatedStates
                 if (Set.count generatedStates % 1000 = 0) then Console.WriteLine (sprintf "%A" (Set.count generatedStates))
                 true
            else false

        // Checks if state is smart and safe before adding to queue
        let AddNewState (s:State) t l = 
            let h = hash s
            match t with
            | Conductor -> AddState s h                   
            | Controller when (IsSmartState s l) && (IsSafeState s)  -> AddState s h
            | _ -> false


        // Creates the control program from a state by backtracking the states
        let rec ToControlProgram s = 
            match s with
            |S(_,sm,tm,rm,x) when x <> N -> s::ToControlProgram x
            | _ -> [s]


        //Function for finding all new states by moving trains in a given state
        //TODO : Look into only looking at moveable train
        let GenerateConductorStates s = 
            match s with
            | S(_,sm,tm,rm,_) -> let nTm = List.fold (fun st (t,d) -> let l = Map.find t st
                                                                      let ps = NextPosition l d sm rm
                                                                      let p = if List.isEmpty ps then l else List.head ps
                                                                      Map.add t p st) tm Trains


                                 let h = CalculateHeuristic nTm Set.empty
                                 let nS = S(h,sm,nTm,rm,s)
                                 if AddNewState nS Conductor Set.empty then set [nS] else Set.empty
            | _ -> failwith "ConductorTurn"


        // Finds all switchrails connected to given location and direction
        let TrainToSwitchRail (l,d) =
            let lns = match d with
                      | L -> Map.find l RWGLeft
                      | R -> Map.find l RWGRight
            let rs = List.fold (fun s v -> (l,v)::s) [] lns
            List.fold (fun s v -> match Map.tryFind v SwitchRails with
                                  | Some(sr) -> Set.add sr s
                                  | _ -> s) Set.empty rs

        // Helper function to find all switch rail combinations
        let rec allCom r sr = 
            match sr with
            | []       -> r
            | x::y::xs -> let r = Set.fold (fun s v -> Set.add (Set.add y v) (Set.add (Set.add x v) s)) Set.empty r
                          allCom r xs
            | _ -> failwith "F"

        // The game
        let rec ControllerTurn _ =
            match PriorityQueue.isEmpty unexploredStatesController with
            | true -> failwith "No more states to explore"
            | _ -> let (s,p) = PriorityQueue.pop unexploredStatesController
                   unexploredStatesController <- p
                   match IsSolved s with
                   | true  ->  (ToControlProgram s)
                   | _ ->      match s with
                               | S(x,_,tm,rm,_) ->   // Find the highest priority of train not yet in goal
                                                     let mp = Map.fold (fun s k v -> if Map.find k tm <> Map.find k Goal then max s v else s) 0 Priorities
                                                     // Pick train with just found priority, or if lower than swappriority pick all remaining trains
                                                     let tp = if MaxPrio >= mp then List.fold (fun s (t,_) -> Set.add t s) Set.empty Trains else Map.fold (fun s k v -> if v = mp then Set.add k s else s) Set.empty Priorities
                                                     // Find signals near all picked trains
                                                     let tSigs = List.fold (fun s (t,d) -> if ((Set.contains t tp) && (Map.containsKey (Map.find t tm,d) SM)) then (Map.find t tm,d)::s else s) [] Trains

                                                     match Set.count tp with
                                                     | 1 -> // Create new states one for each signal being turned on
                                                            let s1 = List.fold (fun sx v -> let nSm = (Map.add (v) true SM)
                                                                                            let locs = set[fst v]
                                                                                            let h = CalculateHeuristic tm locs
                                                                                            let nS = S(h,nSm,tm,rm,s)
                                                                                            if AddNewState nS Controller locs then Set.add nS sx else sx) Set.empty tSigs
                                                            // Find switchrails near picked trains 
                                                            let td = Set.fold (fun s t -> match List.tryFind (fun (t1,d1) -> t1 = t) Trains with
                                                                                          | Some(_,d) -> (Map.find t tm,d)::s
                                                                                          | _ -> s ) [] tp
                                                            let tSR = List.fold (fun s v -> Set.fold (fun sx vx -> Set.add (vx,v) sx) Set.empty (TrainToSwitchRail v) + s) Set.empty td
                                                            // Create new states one for each switchrail change
                                                            let s2 = Set.fold (fun sx (sr,sg) -> let nRm = SwitchRail sr rm
                                                                                                 let locs = (getSwitchRailLocation sr nRm)
                                                                                                 let h = CalculateHeuristic tm locs
                                                                                                 let nSm = Map.add sg true SM
                                                                                                 let nS = S(h,nSm,tm,nRm,s)
                                                                                                 if AddNewState nS Controller locs then Set.add nS sx else sx) Set.empty tSR
                                                            ConductorTurn (s1+s2)
                                                     | _ when MaxPrio >= mp -> // Create new states one for each signal being turned on
                                                                               let s1 = List.fold (fun sx v -> let nSm = (Map.add (v) true SM)
                                                                                                               let locs = set[fst v]
                                                                                                               let h = CalculateHeuristic tm locs
                                                                                                               let nS = S(h,nSm,tm,rm,s)
                                                                                                               if AddNewState nS Controller locs then Set.add nS sx else sx) Set.empty tSigs
                                                                               // Find switchrails near picked trains 
                                                                               let td = Set.fold (fun s t -> match List.tryFind (fun (t1,d1) -> t1 = t) Trains with
                                                                                                             | Some(_,d) -> (Map.find t tm,d)::s
                                                                                                             | _ -> s ) [] tp
                                                                               let tSR = List.fold (fun s v -> Set.fold (fun sx vx -> Set.add (vx,v) sx) Set.empty (TrainToSwitchRail v) + s) Set.empty td
                                                                               // Create new states one for each switchrail change
                                                                               let s2 = Set.fold (fun sx (sr,sg) -> let nRm = SwitchRail sr rm
                                                                                                                    let locs = (getSwitchRailLocation sr nRm)
                                                                                                                    let h = CalculateHeuristic tm locs
                                                                                                                    let nSm = Map.add sg true SM
                                                                                                                    let nS = S(h,nSm,tm,nRm,s)
                                                                                                                    if AddNewState nS Controller locs then Set.add nS sx else sx) Set.empty tSR
                                                                               ConductorTurn (s1+s2)
                                                     | _ -> // Create one new states for all relevant signals being turned on
                                                            let nSm = List.fold (fun s v -> Map.add v true s) SM tSigs
                                                            let locs = List.fold (fun s v -> Set.add (fst v) s) Set.empty tSigs
                                                            let h = CalculateHeuristic tm locs
                                                            let nS = S(h,nSm,tm,rm,s)
                                                            let s1 = if AddNewState nS Controller locs then set [nS] else Set.empty
                                                            // Find switchrails near picked trains 
                                                            let tSR = List.fold (fun s v -> Set.fold (fun sx vx -> Set.add (vx,v) sx) Set.empty (TrainToSwitchRail v) + s) Set.empty tSigs
                                                            // Create new states one for each relevant switchrail combination change
                                                            let srs = Set.fold (fun s (sr,_) -> (sr,true)::(sr,false)::s) [] tSR
                                                            if List.length srs > 0 
                                                            then
                                                                let x = set [List.item 0 srs]
                                                                let y = set [List.item 1 srs]
                                                                let srs = List.tail (List.tail srs)
                                                                let srcom = allCom (Set.add x (Set.add y Set.empty)) srs
                                                            

                                                                let s2 = Set.fold (fun ss v -> let nRm = Set.fold (fun sx (sr,b) -> Map.add sr b sx) rm v
                                                                                               let locs = Set.fold (fun sx (sr,_) -> sx + (getSwitchRailLocation sr nRm)) Set.empty v
                                                                                               let h = CalculateHeuristic tm locs
                                                                                               let nS = S(h,nSm,tm,nRm,s)
                                                                                               if AddNewState nS Controller locs then Set.add nS ss else ss) Set.empty srcom
                                                                ConductorTurn (s1+s2)
                                                            else 
                                                                ConductorTurn s1


                                                     
                               | _ -> failwith "ControllerTurn"

           and ConductorTurn (states:Set<State>) = 
            match Set.isEmpty states with
            | true when PriorityQueue.isEmpty unexploredStatesController -> failwith ("No more states to explore " + string (Set.count generatedStates))
            | true -> ControllerTurn 0
            | _ -> let nStates = Set.fold (fun (s) v -> s + GenerateConductorStates v) (Set.empty) states
                   ConductorTurn nStates
                   
                    

        

        unexploredStatesController <- PriorityQueue.insert s unexploredStatesController
        let r = ControllerTurn 0
        let x = Set.count generatedStates
        List.iter (fun s -> if not (IsSafeState s) then Console.WriteLine(sprintf "Something went wrong") else ()) r


        (r,x)


