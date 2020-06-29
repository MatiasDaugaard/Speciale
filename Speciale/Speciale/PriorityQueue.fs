namespace Railways

open Types

// Implemation of priority queue

module PriorityQueue =

    type PriorityQueue = 
        | Q of (State list)

    // Function to check if queue is empty
    let isEmpty q = 
        match q with
        | Q([]) -> true
        | _ -> false

    // Function to remove first element in queue
    let pop q =
        match q with
        | Q([]) -> failwith "queue is empty"
        | Q(x::xs) -> (x,Q(xs))

    // Helper function to insert new element to correct place in queue
    let rec insertInList s h sl =
        match sl with
        | [] -> [s]
        | x::xs -> match x with
                   | S(hx,_,_,_,_) when hx < h -> x::insertInList s h xs
                   | S(hx,_,_,_,_) -> s::(x::xs)
                   | _ -> failwith "F" 

    // Function to insert element in queue
    //TODO : faster insert
    let insert s q =
        match s,q with
        | (S(h,_,_,_,_),Q(l)) -> Q(insertInList s h l)
        | _ -> failwith "Cannot insert N is queue"


