namespace Railways

module Types =

    type Train = string
    type Direction = L | R
    type Location = int
    type Rail = Location * Location
    type SwitchRail = Location * Location * Location * Direction
    type Signal = Location * Direction
    type RailwayNetwork = Location list * Rail list * SwitchRail list * Signal list * (Train*Location*Location*Direction) list


    type SignalMap = Map<Signal, bool>
    type TrainMap = Map<Train,Location>
    type SwitchRailMap = Map<SwitchRail,bool>
    type State = S of int * SignalMap * TrainMap * SwitchRailMap * State | N

    type RailwayGraph = Map<Location, Location list>
    type DistanceMap = Map<Location*Location,int>
    type Turn = Controller | Conductor
    type StateID = int




