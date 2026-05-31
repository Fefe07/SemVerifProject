(* 


(* TODO : modify VALUE_DOMAIN to add a collapse function *)
(* TODO : implement disjunctive domain collapse in wished domain (possible to create a collapse <ith a functor ?) *)
(* How do I decide where to partition ? Take 0 and thresholds instead of random values *)
(* What is this directive thing ? Just a on/off or a breakpoint indication ? *)
(* In partitioning, do we keep the disjunctino structure and collapse once in a while or have a map partition -> t *)
(* A map partition -> t would be more direct but more *)
open ValueDomain
open IntervalDomain
open Z


module OrderedIntervals  = struct
  type t = IntervalValueDomain.t 

  let compare_bound (a : IntervalValueDomain.bound) (b : IntervalValueDomain.bound) = 
    match a,b with 
    | NEG_INF, NEG_INF 
    | POS_INF, POS_INF -> 0 
    | NEG_INF, _ | _, POS_INF -> -1
    | _, NEG_INF | POS_INF, _ -> 1 
    | INT_BOUND x, INT_BOUND y -> Z.compare x y

  let compare x y = 
    let z = compare_bound (fst x) (fst y) in 
    if z = 0 then compare_bound (snd x) (snd y) else z
end
module DisjunctiveDomainDerivation (A : VALUE_DOMAIN) : VALUE_DOMAIN = struct

  (* Remark : relevant parts are complettely different for various domains *)

  module Pmap = Map.Make(OrderedIntervals)

  type t = A.t Pmap.t

  let intervals : IntervalValueDomain.t list = [(NEG_INF, INT_BOUND one)]

  (* let top = Pmap.empty  *)

  (* type t = (IntervalValueDomain.t  * A.t) list  *)
  
  
  
  

end *)