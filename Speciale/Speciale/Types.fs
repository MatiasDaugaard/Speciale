namespace Railways

module Types =
    // Type declarations
    type Train = string
    type Direction = L | R
    type Location = int
    type Rail = Location * Location
    type SwitchRail = Location * Location * Location * Direction
    type Turn = Controller | Conductor
    type Signal = Location * Direction


    // List of Location (Nodes), Rails (Vertex), SplitRail (Vertex), Signal (Signals), T*L*L*D (Train,Start,End,Direction)
    type RailwayNetwork = Location list * Rail list * SwitchRail list * Signal list * (Train*Location*Location*Direction) list
    type RailwayGraph = Map<Location, Location list>

    type SignalMap = Map<Signal, bool>
    type TrainMap = Map<Train,Location>
    type SwitchRailMap = Map<SwitchRail,bool>
    type DistanceMap = Map<Location*Location,int>

    type StateID = int

    type State = S of int * SignalMap * TrainMap * SwitchRailMap * State | N

    //type StateMap = Map<StateID,State>