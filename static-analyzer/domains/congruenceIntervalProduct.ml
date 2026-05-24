
open ReducedProductDomain
open CongruenceDomain
open IntervalDomain

let real_div x y = 
  if x >= 0 then x/y 
  else x/y + 1  

module A = IntervalValueDomain
module B = CongruenceValueDomain

let red ((i, z) : A.t * CongruenceValueDomain.t)  : (A.t * CongruenceValueDomain.t) =
  match i,z with 
  | _,Bottom -> A.bottom, CongruenceValueDomain.bottom 
  | (_,POS_INF), _ | (NEG_INF, _) -> i,z 
  | (POS_INF, NEG_INF) -> A.bottom, CongruenceValueDomain.bottom
  | (INT_BOUND a,INT_BOUND b),V(c,d) -> begin 
  let a' = real_div (a-d -1) (abs c) in (* I think this formula works*) 
  let b' = real_div (b-d) (abs c) in
  if a' = b' then A.bottom, CongruenceValueDomain.bottom
  else if a' = b' - 1 then b' * (abs c) + d  
  else (i,z)
end

module M = struct
  module A = IntervalValueDomain
  module B = CongruenceValueDomain 
  let reduction = red 
end

module CongruenceIntervalProduct = 
  ReducedProductDomain(M) 