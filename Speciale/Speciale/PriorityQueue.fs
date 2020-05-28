namespace Railways

open Types

module PriorityQueue =

    type PriorityQueue = 
        | Q of (State list)


    let isEmpty q = 
        match q with
        | Q([]) -> true
        | _ -> false

    let pop q =
        match q with
        | Q([]) -> failwith "queue is empty"
        | Q(x::xs) -> (x,Q(xs))


    let rec insertInList s h sl =
        match sl with
        | [] -> [s]
        | x::xs -> match x with
                   | S(hx,_,_,_,_) when hx < h -> x::insertInList s h xs
                   | S(hx,_,_,_,_) -> s::(x::xs)
                   | _ -> failwith "F" 

    //TODO : faster insert
    let insert s q =
        match s,q with
        | (S(h,_,_,_,_),Q(l)) -> Q(insertInList s h l)
        | _ -> failwith "Cannot insert N is queue"


