namespace Railways

module Types =
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

    type StateID = int

    type State = S of int * SignalMap * TrainMap * SplitRailMap * State * Set<Location> | N

    type StateMap = Map<StateID,State>