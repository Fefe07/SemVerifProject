(* Product of interval and congruence domain *)



(* Functor for getting the reduced product of two Value Domains *)
(* Give identity as reduction to get the usual product*)
(* Cannot make a functor :(, you have to copy-paste this and replace A,B and red manually *)


open ValueDomain
open CongruenceDomain
open IntervalDomain
open Domain
open ValueDomainDerivation
open Z

(* module type M  = sig 
  module A 
  module B 
  val reduction : (A.t * B.t) -> (A.t * B.t)
end *)


module IntervalCongruenceValueDomain 
(* ( M  : sig 
  module A 
  module B 
  val reduction : (A.t * B.t) -> (A.t * B.t)
end)
: VALUE_DOMAIN  *) =
struct 
  module A = IntervalValueDomain
  module B = CongruenceValueDomain
  let real_div (x:Z.t) (y:Z.t) : Z.t = 
    if x >= Z.zero then x/y 
    else x/y + Z.one  
  
  let red ((i, z) : A.t *B.t)  : (A.t * B.t) =
    match i,z with 
    | _,Bottom -> A.bottom, CongruenceValueDomain.bottom 
    | (_,POS_INF), _ | (NEG_INF, _), _ -> i,z 
    | (POS_INF,  _), _ | (_,NEG_INF) , _-> A.bottom, CongruenceValueDomain.bottom
    | (INT_BOUND a,INT_BOUND b),V(c,d) -> begin 
      if c = zero then begin 
        if a <= d && d <= b then (A.const d, B.const d)
        else A.bottom, B.bottom
      end else 
      let a' = real_div (a-d -one) (abs c) in (* I think this formula works*) 
      let b' = real_div (b-d) (abs c) in
      if a' = b' then A.bottom, CongruenceValueDomain.bottom
      else if a' = b' - one then (A.const (b' * (abs c) + d), B.const(b' * (abs c) + d))  
      else (i,z)
    end

  type t = A.t * B.t 

  let top = (A.top, B.top) 

  let bottom = (A.bottom , B.bottom)

  let const x = A.const x, B.const x 
  
  let rand x y = (A.rand x y, B.rand x y)

  (* I'm not sure it is useful to apply red here, but it is correct *)
  (* Same reflections for the next functions*)
  let unary (a,b) unop = 
    red (A.unary a unop, B.unary b unop)

  let binary (a,b) (c,d) binop = 
    red( A.binary a c binop, B.binary b d binop)

  let compare (a,b) (c,d) cmp = 
    let (a',c') = A.compare a c cmp in 
    let (b',d') = B.compare b d cmp in 
    (red (a', b'), red(c', d'))

  let bwd_unary (a,b) unop (c,d) = 
    let a' = A.bwd_unary a unop c in 
    let b' = B.bwd_unary b unop d in 
    red (a',b')

  let bwd_binary (a,b) (c,d) unop (e,f) = 
    let (a',c') = A.bwd_binary a c unop e in 
    let (b',d') = B.bwd_binary b d unop f in 
    (red(a',b'), red(c',d'))


  let join (a,b) (c,d) = 
    red(A.join a c, B.join b d)

  let meet (a,b) (c,d) = 
    red(A.meet a c, B.meet b d)

  (* Must NOT use the reduction, else we lose the widening effect *)
  let widen (a,b) (c,d) = 
    A.widen a c, B.widen b d 

  let narrow (a,b) (c,d) = 
    A.narrow a c, B.narrow b d 

  let leq (a,b) (c,d) = 
    A.leq a c && B.leq b d 

  (* Returns true if (a,b) is semantically equal to bottom*)
  (* i.e if a = bot or b = bot*)
  let is_bottom (a,b) = 
    A.is_bottom  a || B.is_bottom b

  let pp fmt (a,b) = 
    Format.pp_print_string fmt "(" ; 
    A.pp fmt a ;
    Format.pp_print_string fmt " , " ;
    B.pp fmt b ;
    Format.pp_print_string fmt ")" ;




end

module Make(Vars : VARS) : DOMAIN =
    ValueDomainDerivation(IntervalCongruenceValueDomain)(Vars)
