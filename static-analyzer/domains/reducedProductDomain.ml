(* Functor for getting the reduced product of two Value Domains *)
(* Give identity as reduction to get the usual product*)


open ValueDomain

(* module type M  = sig 
  module A 
  module B 
  val reduction : (A.t * B.t) -> (A.t * B.t)
end *)

module ReducedProductDomain 
(* ( M  : sig 
  module A 
  module B 
  val reduction : (A.t * B.t) -> (A.t * B.t)
end)
: VALUE_DOMAIN  *) =
struct 
  module A 
  module B 
  let red = M.reduction

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