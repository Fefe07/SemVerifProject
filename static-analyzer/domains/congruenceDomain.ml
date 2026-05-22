(* Congruence Domain *)

open Domain
open ValueDomain
open ValueDomainDerivation
open Z

module SignValueDomain : VALUE_DOMAIN = struct

    type t = V of Z.t * Z.t | Bottom

    let top = V(Z.one,Z.zero)

    let bottom = Bottom

    let is_bottom s = s = Bottom

    let neg = function
        | Bottom -> Bottom 
        | V(a,b) -> V(a,- b)
 

    let add s r =
        match s,r with 
        | Bottom, _ | _, Bottom -> Bottom 
        | V(a,b), V(a',b') -> 
          V(gcd a a', b + b')


    let sub s r = add s (neg r)

    let mult s r =
        match s, r with
        | Bottom, _ | _, Bottom -> Bottom
        | V(a,b), V(a',b') ->
          V(gcd (gcd (a*a') (a*b')) b*a' , b*b')


    let div s r = 
      match s, r with
        | Bottom, _ | _, Bottom -> Bottom
        | V(a,b), V(a',b') -> 
          if a'=Z.zero && b' = Z.zero then Bottom 
          else 
            if a' = Z.zero && b' <> Z.zero && b' mod a = Z.zero && b' mod b = Z.zero then 
            V(a / (abs b'), b/b')
        else top

    let modulo s r = 
      match s,r with 
      | Bottom, _ | _, Bottom -> Bottom
      | V(a,b), V(a',b') ->
        if a' = Z.zero && a mod b' = zero then begin 
          V(zero, b mod b')
        end else top

    let const (z : Z.t) : t =
        V(Z.zero,z)

    let rand (a : Z.t) (b : Z.t) : t =
        if a = b then const a else top

    let unary (s : t) iuop : t= Frontend.AbstractSyntax.(
        match iuop with
        | AST_UNARY_PLUS -> s
        | AST_UNARY_MINUS -> neg s
    )

    let binary (s : t) (r : t) ibop : t = Frontend.AbstractSyntax.(
        match ibop with
        | AST_PLUS -> add
        | AST_MINUS -> sub
        | AST_MULTIPLY -> mult
        | AST_DIVIDE -> div
        | AST_MODULO -> modulo
    ) s r

    let leq (s : t) (r : t) : bool =
        match s, r with
        | Bottom, _ -> true 
        | _,Bottom -> false 
        | V(a,b), V(a', b') ->
          (a mod a' = Z.zero) && (b-b' mod a' = Z.zero)

    let join (s : t) (r : t) : t =
      match s, r with
      | Bottom, x | x, Bottom -> x
      | V(a,b), V(a',b') ->
        V(Z.gcd (Z.gcd a a') (abs (b-b')), b)

    let rec euclide a a' = 
      if a < a' then euclide a' a 
      else let x = gcd a a' in if x>one then euclide (a/x) (a'/x)
      else if a' = Z.one then (Z.zero,Z.one)
      else if a' = Z.zero then failwith "Erreur euclide"
      else begin 
        let (x,y) = euclide a' (a mod a') in 
        (y, x - (y * (a/a')) )
      end

    let meet (s : t) (r : t) : t =
        match s, r with
        | Bottom, _ | _, Bottom -> Bottom
        | V(a,b), V(a',b') ->
          if b-b' mod (gcd a a') = zero then 
            let (x,y) = euclide a a' in
            let b'' = b + (b' - b)/(gcd a a')*x*a  in 
            V(lcm a a', b'')
          else Bottom 

    let compare (s : t) (r : t) cop : t * t = Frontend.AbstractSyntax.(
        match cop with
        | AST_EQUAL ->
            let x = meet s r in (x,x) 
        | AST_NOT_EQUAL -> begin
            match s,r with 
            | Bottom, _  -> Bottom, r 
            | _,Bottom -> s, Bottom 
            | V(a,b), V(a',b') when a = Z.zero && a' = Z.zero && b = b' ->  Bottom,Bottom 
            | _ -> s,r
        end
        | AST_LESS -> begin
          match s,r with 
          | Bottom, _  -> Bottom, r 
          | _,Bottom -> s, Bottom 
          | V(a,b), V(a',b') when a = Z.zero && a' = Z.zero && b >= b' ->  Bottom,Bottom 
          | _ -> s,r
        end
        | AST_LESS_EQUAL -> begin
          match s,r with 
          | Bottom, _  -> Bottom, r 
          | _,Bottom -> s, Bottom 
          | V(a,b), V(a',b') when a = Z.zero && a' = Z.zero && b > b' ->  Bottom,Bottom 
          | _ -> s,r
        end
        | AST_GREATER -> begin
          match s,r with 
          | Bottom, _  -> Bottom, r 
          | _,Bottom -> s, Bottom 
          | V(a,b), V(a',b') when a = Z.zero && a' = Z.zero && b <= b' ->  Bottom,Bottom 
          | _ -> s,r
        end
        | AST_GREATER_EQUAL -> begin
          match s,r with 
          | Bottom, _  -> Bottom, r 
          | _,Bottom -> s, Bottom 
          | V(a,b), V(a',b') when a = Z.zero && a' = Z.zero && b < b' ->  Bottom,Bottom 
          | _ -> s,r
        end
    )

    let bwd_unary (s : t) iuop (target : t) : t = Frontend.AbstractSyntax.(
        match iuop with
        | AST_UNARY_PLUS -> meet s target
        | AST_UNARY_MINUS -> meet s (neg target)
    )

    let bwd_binary (s : t) (r : t) ibop (target : t) : t * t =
    Frontend.AbstractSyntax.(
        match ibop with
        | AST_PLUS ->
            meet s (sub target r), meet r (sub target s)
        | AST_MINUS ->
            meet s (add target r), meet r (sub s target)
        | AST_MULTIPLY ->
            meet s (div target r), meet r (div target s)
        | AST_DIVIDE -> 
          meet s (mult target r), meet r (div s target) 
        | AST_MODULO -> s, r (* Not implemented *)
    )

    (* Pas de chaine infinie strictement croissante (a decroit) donc pas besoin*)
    let widen : t -> t -> t = join

    let narrow s r = 
      match s,r with 
      | Bottom, _ | _ , Bottom -> Bottom 
      | V(a,b), V(a',b') -> if a = Z.zero then r else s

    let pp (formatter : Format.formatter) (s : t) : unit =
        Format.pp_print_string formatter (
            match s with
            | Bottom -> "bottom"
            |V(a,b) -> Z.to_string a ^ "Z + " ^ Z.to_string b 
        )

end


module Make(Vars : VARS) : DOMAIN =
    ValueDomainDerivation(SignValueDomain)(Vars)

