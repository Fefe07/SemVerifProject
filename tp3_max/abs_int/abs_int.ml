(* Interval abstract domain *)

type bound =
    | NEG_INF
    | POS_INF
    | INT_BOUND of Z.t

type t = bound * bound

let bottom = (POS_INF, NEG_INF)
let top = (NEG_INF, POS_INF)

let zero = INT_BOUND Z.zero

let const_abs (k : Z.t) = (INT_BOUND k, INT_BOUND k)

let interval (a : Z.t) (b : Z.t) = (INT_BOUND a, INT_BOUND b)


let equal i1 i2 = i1 = i2

let neg_bound = function
    | NEG_INF -> POS_INF
    | POS_INF -> NEG_INF
    | INT_BOUND z -> INT_BOUND (Z.neg z)

let neg ((b1, b2) : t) = (neg_bound b2, neg_bound b1)

let add_bounds b1 b2 = match b1, b2 with
    | NEG_INF, POS_INF | POS_INF, NEG_INF -> failwith "add_bounds failure"
    | _, POS_INF | POS_INF, _ -> POS_INF
    | NEG_INF, _ | _, NEG_INF -> NEG_INF
    | INT_BOUND z1, INT_BOUND z2 -> INT_BOUND (Z.add z1 z2)

let add (b1, b2) (c1, c2) =
    if (b1, b2) = bottom || (c1, c2) = bottom then bottom else
    (add_bounds b1 c1, add_bounds b2 c2)

let sub i1 i2 = add i1 (neg i2)


let leq_bounds b1 b2 = match b1, b2 with
    | _, POS_INF -> true
    | NEG_INF, _ -> true
    | INT_BOUND z1, INT_BOUND z2 -> Z.leq z1 z2
    | _ -> false

let compare_bounds b1 b2 = match b1, b2 with
    | POS_INF, POS_INF | NEG_INF, NEG_INF -> 0
    | _, POS_INF | NEG_INF, _ -> -1
    | POS_INF, _ | _, NEG_INF -> 1
    | INT_BOUND z1, INT_BOUND z2 -> Z.compare z1 z2


let max_bounds =
    List.fold_left (fun a b -> if leq_bounds a b then b else a) NEG_INF

let min_bounds =
    List.fold_left (fun a b -> if leq_bounds a b then a else b) POS_INF

let mult_bounds b1 b2 = 
    if b1 = zero || b2 = zero then zero else
    match b1, b2 with
    | NEG_INF, POS_INF | POS_INF, NEG_INF -> NEG_INF
    | POS_INF, POS_INF | NEG_INF, NEG_INF -> POS_INF
    | POS_INF, INT_BOUND z | INT_BOUND z, POS_INF ->
            if Z.compare z Z.zero = 1 then POS_INF else NEG_INF
    | NEG_INF, INT_BOUND z | INT_BOUND z, NEG_INF ->
            if Z.compare z Z.zero = 1 then NEG_INF else POS_INF
    | INT_BOUND z1, INT_BOUND z2 -> INT_BOUND (Z.mul z1 z2)

let mult (b1, b2) (c1, c2) =
    let l =
        [mult_bounds b1 c1; mult_bounds b1 c2; mult_bounds b2 c1; mult_bounds b2 c2]
    in
    (min_bounds l, max_bounds l)

(* Join *)
let join (a1, a2) (b1, b2) =
    min_bounds [a1; a2; b1; b2],
    max_bounds [a1; a2; b1; b2]




let div_bounds n d = (* d is stricly positive *)
    match n, d with
    | INT_BOUND a, INT_BOUND b -> INT_BOUND (Z.div a b)
    | POS_INF, _ -> POS_INF
    | NEG_INF, _ -> NEG_INF
    | _ -> zero

let div_pos (b1, b2) (c1, c2) =
    (* Division of intervals assuming c1, c2 > 0 *)
    begin
        if leq_bounds zero b1 then div_bounds b1 c2
        else div_bounds b1 c1
    end,
    begin
        if leq_bounds zero b2 then div_bounds b2 c1
        else div_bounds b2 c2
    end

let rec div i1 (c1, c2) =
    let a,b = compare_bounds c1 zero,compare_bounds c2 zero in
    match a/(abs a), b / (abs b) with
    | 1, 1 -> div_pos i1 (c1, c2)
    | -1, -1 -> neg @@ div_pos i1 (neg (c1, c2))
    | 1, -1 | 1,0 | 0, -1 -> bottom
    (* | _ -> failwith "division by 0" *)
    (* This part works if we do not want to raise errors, 
       but to treat only non-error executions *)
    | 0, 0 -> failwith "division by 0"
    | 0 , 1 -> div i1 (INT_BOUND Z.one, c2)
    | -1, 0 -> div i1 (c1, INT_BOUND (Z.of_int (-1)))
    | -1,1 -> join (div i1 (c1,INT_BOUND (Z.of_int (-1)))) (div i1 (INT_BOUND Z.one,c2))
    | _ -> assert(false) (* Impossible *)

let modulo_pos (b1, b2) (c1, c2) =
    if leq_bounds zero b1
    then
        if leq_bounds b2 c1
        then
            (b1, b2)
        else
            if leq_bounds b2 c2
            then
                (zero, b2)
            else
                (zero, c2)
    else
        (zero, c2)

let modulo i1 (c1, c2) =
    match
        compare_bounds c1 zero,
        compare_bounds c2 zero
    with
    | 1, 1 -> modulo_pos i1 (c1, c2)
    | -1, -1 -> neg @@ modulo_pos i1 (neg (c1, c2))
    | _ -> failwith "division by 0"


(* Backward Abstract Semantics *)

let check (a, b) =
    if compare_bounds a b = 1 then bottom else (a, b)

let bas_leq a b : t * t =
    (* Updates ranges a and b by adding the constraint a<=b *)
    let (a1, a2), (b1, b2) = a, b in
    (* If a1 > b2 it is impossible *)
    if compare_bounds a1 b2 >= 1 then bottom, bottom else
    ( if compare_bounds a2 b2 <= 0 then a else (a1, b2) ),
    ( if compare_bounds a1 b1 <= 0 then b else (a1, b2) )

let succ_bound = function
    | POS_INF | NEG_INF as b-> b
    | INT_BOUND z -> INT_BOUND (Z.succ z)

let pred_bound = function
    | POS_INF | NEG_INF as b-> b
    | INT_BOUND z -> INT_BOUND (Z.pred z)


let bas_lt a b : t * t =
    let (a1, a2), (b1, b2) = a, b in
    if compare_bounds a1 b2 >= 0 then bottom, bottom else
    ( if compare_bounds a2 b2 < 0 then a else (a1, pred_bound b2) ),
    ( if compare_bounds a1 b1 < 0 then b else (succ_bound a1, b2) )

let bas_geq a b = let x, y = bas_leq b a in y, x

let bas_gt a b = let x, y = bas_lt b a in y, x

let bas_eq a b = 
    let (a1, a2), (b1, b2) = a, b in
    if compare_bounds a1 b2 > 0 then bottom else
    if compare_bounds a2 b1 < 0 then bottom else
    ( if compare_bounds a1 b1 < 0 then b1 else a1 ),
    ( if compare_bounds a2 b2 < 0 then a2 else b2 )

let inter = bas_eq

(* Widen *)
let widen (a1, a2) (b1, b2) =
    ( if compare a1 b1 <= 0 then a1 else NEG_INF ),
    ( if compare a2 b2 >= 0 then a2 else POS_INF )


(* Pretty printer *)

let pp_bound formatter = function
    | POS_INF -> Format.pp_print_string formatter "+inf"
    | NEG_INF -> Format.pp_print_string formatter "-inf"
    | INT_BOUND z-> Z.pp_print formatter z

let pp formatter (a, b) =
    Format.fprintf formatter "@[[%a; %a]@]" pp_bound a pp_bound b


