namespace Railways

open System
open Railways.Types
open Railways.Preprocess
open Railways.PriorityQueue
open Railways.Postprocess

module BestFirst =

    

    let Solve rn = 

        // Used to time preprocess
        let stopWatchPre = System.Diagnostics.Stopwatch.StartNew()

        // Getting global variable from preprocessing
        let Trains, RWGLeft, RWGRight, Goals, DistanceMap, Pathss, SwitchRails, Priorities, MaxPrio, SM, s = InitiateState rn

        // Datastructures used to keep track of current goals and paths
        let mutable Goal = List.head Goals
        let mutable Paths = List.head Pathss
        // Datastructure used to keep track of visited and non visited states
        let mutable unexploredStatesController:PriorityQueue = Q([])
        //Datastructure used to keep track of already seen states
        let mutable generatedStates:Set<StateID> = Set.empty

        stopWatchPre.Stop()
        let pretime = stopWatchPre.Elapsed.TotalMilliseconds

        // Function for hashing a state
        let hash s = 
            match s with
            | S(_,sm,tm,rm,_) -> Map.fold (fun s (a,b,c,d) v -> hash(s,a,b,c,d,v)) (Map.fold (fun s t l -> hash(s,t,l)) (Map.fold (fun s (l,d) b -> hash(s,l,d,b)) 0 sm) tm) rm
            | _ -> failwith "Cannot hash N"    

        // Function used to update the goal map
        let rec NextGoal g gl =
            match gl with
            | [] -> failwith "F"
            | x::xs when x = g -> List.head xs
            | _::xs -> NextGoal g xs

        // Checks if all trains are in their goal positions if so checks if final goal if so returns true otherwise updates goals
        let IsSolved (s:State) =  
            match s with
            | S(_,_,tm,_,_) -> match Map.forall (fun t l -> Map.find t tm = l) Goal with
                               | true -> if List.last Goals = Goal 
                                         then 
                                             true 
                                         else 
                                             Goal <- NextGoal Goal Goals
                                             Paths <- NextGoal Paths Pathss
                                             unexploredStatesController <- Q([s])
                                             false
                               | false -> false
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
        let ChangeSwitchRail (sr:SwitchRail) (rm:SwitchRailMap) = 
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

        // Checks if trains can reach other trains, can go off path or reach location reachable by other train, if true state is not safe  
        let IsSafeState (s:State) =
            match s with
            | S(_,sm,tm,rm,_) -> let arl = List.fold (fun s (t,d) -> Map.add t (ReachableLocations t d sm tm rm) s) Map.empty Trains
                                 List.forall (fun (t,d) -> //Locations currently picked train can reach 
                                                           let rl = Map.find t arl

                                                           // Locations which other trains can reach
                                                           let rls = Map.fold (fun s k v -> if k = t 
                                                                                            then 
                                                                                                s
                                                                                            else 
                                                                                                Set.union s v) Set.empty arl

                                                           let tloc = Set.remove (Map.find t tm) (Preprocess.valueSet tm)
                                                           let locs = Set.union rls tloc

                                                           // Should not be able to reach another train, or same location as other train
                                                           let b1 = Set.intersect rl locs = Set.empty

                                                           // Should not be able to reach location not on path
                                                           let b2 = Set.difference rl (Map.find t Paths) = Set.empty

                                                           b1 && b2) Trains
            | _ -> failwith "IsSafeState N"


        //Calculates total distance for the trains current position to their goal times the priority of the train
        let CalculateHeuristic (tm:TrainMap) = 
            List.fold (fun s (t,d) -> let l = Map.find t tm
                                      let g = Map.find t Goal
                                      if l = g then s else

                                      s +  (Map.find (l,g) DistanceMap)
                                      ) 0 Trains

                                      
        // Add state to the queues if it has not been added before
        let AddState s h = 
            if not (Set.contains h generatedStates)
            then unexploredStatesController <- PriorityQueue.insert s unexploredStatesController
                 generatedStates <- Set.add h generatedStates
                 true
            else false

        // Checks if state is smart and safe before adding to queue
        let AddNewState (s:State) t = 
            let h = hash s
            match t with
            | Conductor -> AddState s h                 
            | Controller when (IsSafeState s)  -> AddState s h
            | _ -> false


        // Creates the control program from a state by backtracking the states
        let rec ToControlProgram s = 
            match s with
            |S(_,sm,tm,rm,x) when x <> N -> s::ToControlProgram x
            | _ -> [s]


        //Function for finding all new states by moving trains in a given state
        let GenerateConductorStates s = 
            match s with
            | S(_,sm,tm,rm,_) -> let nTm = List.fold (fun st (t,d) -> let l = Map.find t st
                                                                      let ps = NextPosition l d sm rm
                                                                      let p = if List.isEmpty ps then l else List.head ps
                                                                      Map.add t p st) tm Trains


                                 let h = CalculateHeuristic nTm 
                                 let nS = S(h,sm,nTm,rm,s)
                                 if AddNewState nS Conductor then set [nS] else Set.empty
            | _ -> failwith "Cannot generate new states from N"


        // Finds all switchrails connected to given location and direction
        let TrainToSwitchRail (l,d) =
            let lns = match d with
                      | L -> Map.find l RWGLeft
                      | R -> Map.find l RWGRight
            let rs = List.fold (fun s v -> (l,v)::s) [] lns
            List.fold (fun s v -> match Map.tryFind v SwitchRails with
                                  | Some(sr) -> Set.add sr s
                                  | _ -> s) Set.empty rs
                                  
        //Function to open entire path for a train, turn on all signals and switch switchrails correctly
        let OpenPath t d (sm:SignalMap) (rm:SwitchRailMap) =
            let ps = Map.find t Paths
            let nSm = Set.fold (fun s v -> let sign = (v,d)
                                           match Map.tryFindKey (fun k _ -> k=sign) sm with
                                           | Some(x) when fst x <> Map.find t Goal ->  Map.add x true s
                                           | _ -> s) sm ps
            let nRm = Set.fold (fun s v -> let rwg = match d with
                                                     | R -> RWGRight
                                                     | L -> RWGLeft
                                           let nps = Set.intersect (Set.ofList (Map.find v rwg)) ps
                                           match Set.isEmpty nps with
                                           | true -> s
                                           | false -> let np = Set.minElement nps
                                                      match CanMove (v,np) d nSm rm with
                                                      | true -> s
                                                      | false -> let sr = Map.find (v,np) SwitchRails
                                                                 ChangeSwitchRail sr s) rm ps
            nSm,nRm

        // Helper function to find all switch rail combinations
        let rec AllCom r sr = 
            match sr with
            | []       -> r
            | x::y::xs -> let r = Set.fold (fun s v -> Set.add (Set.add y v) (Set.add (Set.add x v) s)) Set.empty r
                          AllCom r xs
            | _ -> failwith "AllCom failed"

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
                                                     let curPrio = Map.fold (fun s k v -> if Map.find k tm <> Map.find k Goal then max s v else s) 0 Priorities
                                                     // Pick train with just found priority, or if lower than non-priority value pick all remaining trains
                                                     let prioTs = if MaxPrio >= curPrio 
                                                                  then List.fold (fun s (t,_) -> if Map.find t tm <> Map.find t Goal then Set.add t s else s) Set.empty Trains 
                                                                  else Map.fold (fun s k v -> if v = curPrio && Map.find k tm <> Map.find k Goal then Set.add k s else s) Set.empty Priorities
                                                     // Find signals near all picked trains
                                                     let tSigs = List.fold (fun s (t,d) -> if ((Set.contains t prioTs) && (Map.containsKey (Map.find t tm,d) SM)) then (Map.find t tm,d)::s else s) [] Trains
                                                     //Find location and direction of picked trains
                                                     let td = Set.fold (fun s t -> match List.tryFind (fun (t1,d1) -> t1 = t) Trains with
                                                                                   | Some(_,d) -> (Map.find t tm,d)::s
                                                                                   | _ -> s ) [] prioTs
                                                     let tls = List.fold (fun s (l,_) -> Set.add l s) Set.empty td
                                                     match Set.count prioTs with
                                                     | x when MaxPrio >= curPrio ->

                                                            // Create new states. One for each signal near train being turned on
                                                            let s1 = List.fold (fun sx v -> let nSm = (Map.add (v) true SM)
                                                                                            let h = CalculateHeuristic tm 
                                                                                            let nS = S(h,nSm,tm,rm,s)
                                                                                            if AddNewState nS Controller then Set.add nS sx else sx) Set.empty tSigs


                                                            // Find switchrails near trains
                                                            let tSR = List.fold (fun s v -> Set.fold (fun sx vx -> Set.add (vx,v) sx) Set.empty (TrainToSwitchRail v) + s) Set.empty td

                                                            // Create new states one for each switchrail change
                                                            let s2 = Set.fold (fun sx (sr,sg) -> let nRm = ChangeSwitchRail sr rm
                                                                                                 let locs = (getSwitchRailLocation sr nRm)
                                                                                                 let b = not (Set.isEmpty (Set.intersect locs tls))

                                                                                                 let h = CalculateHeuristic tm 
                                                                                                 let nSm = Map.add sg true SM
                                                                                                 let nS = S(h,nSm,tm,nRm,s)
                                                                                                 if b && AddNewState nS Controller then Set.add nS sx else sx) Set.empty tSR
                                                            
                                                            ConductorTurn (s1+s2)
                                                     // The block below should be uncommented if the version opening all signals on paths for trains should be used
                                                     // ####################################
                                                     // START OF OPENING ENTIRE PATHS SOLVER
                                                     (*
                                                     | _ -> // Uncomment line below for single agent entire paths solver
                                                            //let prioTs = set [Set.minElement prioTs]
                                                            let nSm,nRm = Set.fold (fun (ssm,srm) t ->  let t = t
                                                                                                        let _,d = List.find (fun (l,d) -> l = Map.find t tm) td
                                                                                                        OpenPath t d ssm srm) (SM,rm) prioTs
                                                            let h = CalculateHeuristic tm
                                                            let nS = S(h,nSm,tm,nRm,s)
                                                            let s1 = if AddNewState nS Controller  then set [nS] else Set.empty
                                                            ConductorTurn s1
                                                     *) 
                                                     // END OF OPENING ENTIRE PATHS SOLVER
                                                     // ##################################

                                                     // The block below should be uncommented if the version opening only signals at same location as trains should be used
                                                     // #####################################
                                                     // START OF SINGLE SIGNAL OPENING SOLVER
                                                     //(*
                                                     | _ ->
                                                        
                                                        let tSigs = [List.head tSigs]
                                                        // Create one new states for all relevant signals being turned on
                                                        let nSm = List.fold (fun s v -> Map.add v true s) SM tSigs
                                                        let h = CalculateHeuristic tm 
                                                        let nS = S(h,nSm,tm,rm,s)
                                                        let s1 = if AddNewState nS Controller  then set [nS] else Set.empty
                                                        // Find switchrails near picked trains 
                                                        let tSR = List.fold (fun s v -> Set.fold (fun sx vx -> Set.add (vx,v) sx) Set.empty (TrainToSwitchRail v) + s) Set.empty tSigs
                                                        // Create new states one for each relevant switchrail combination change
                                                        let srs = Set.fold (fun s (sr,_) -> (sr,true)::(sr,false)::s) [] tSR
                                                        if List.length srs > 0 
                                                        then
                                                            let x = set [List.item 0 srs]
                                                            let y = set [List.item 1 srs]
                                                            let srs = List.tail (List.tail srs) 
                                                            let srcom = AllCom (Set.add x (Set.add y Set.empty)) srs

                                                            let s2 = Set.fold (fun ss v -> let nRm = Set.fold (fun sx (sr,b) -> Map.add sr b sx) rm v
                                                                                           let locs = Set.fold (fun sx (sr,_) -> sx + (getSwitchRailLocation sr nRm)) Set.empty v
                                                                                           let h = CalculateHeuristic tm 
                                                                                           let nS = S(h,nSm,tm,nRm,s)
                                                                                           let b = not (Set.isEmpty (Set.intersect locs tls))
                                                                                           if b && AddNewState nS Controller then Set.add nS ss else ss) Set.empty srcom
                                                            ConductorTurn (s1+s2)
                                                        else 
                                                            ConductorTurn s1
                                                     //*)
                                                     // END OF SINGLE SIGNAL OPENING SOLVER
                                                     // ###################################
                                                      
                               | _ -> failwith "ControllerTurn"

           and ConductorTurn (states:Set<State>) = 
            match Set.isEmpty states with
            | true -> ControllerTurn 0
            | _ -> let nStates = Set.fold (fun (s) v -> s + GenerateConductorStates v) (Set.empty) states
                   ConductorTurn nStates
                   
                    

        // Used to time the solving
        let stopWatchSolve = System.Diagnostics.Stopwatch.StartNew()

        unexploredStatesController <- PriorityQueue.insert s unexploredStatesController
        AddNewState s Conductor |> ignore
        let r = ControllerTurn 0
        let x = Set.count generatedStates

        stopWatchSolve.Stop()
        let solvetime = stopWatchSolve.Elapsed.TotalMilliseconds

        let postresult = r
        // Used to time the postprocessing
        let stopWatchPost = System.Diagnostics.Stopwatch.StartNew()
        // Line below used multiagent postprocess for opening entire paths solver
        //let postresult = if Set.contains 0 (valueSet Priorities) then r else CombineSolutionEntirePath r

        // Line below used multiagent postprocess for opening single signal solver
        let postresult = if Set.contains 0 (valueSet Priorities) then r else CombineSolutionSingleSignal r Trains

        stopWatchPost.Stop()
        let posttime = stopWatchPost.Elapsed.TotalMilliseconds

        let rec CheckSafeness l =
            match l with
            | [] -> ()
            | x::xs -> match IsSafeState x with
                       | false -> Console.WriteLine(sprintf "Something went wrong")
                                  CheckSafeness xs
                       | true -> CheckSafeness xs
                       

        Paths <- Map.fold (fun s k v -> Map.add k (v+Map.find k s) s) Paths (List.head Pathss)
        CheckSafeness postresult
        (postresult,x,pretime,solvetime,posttime)



