(* Sign Domain *)
(* First a sign value domain is defined,
   then the interval domain is derived by ValueDomainDerivation *)

open Domain
open ValueDomain
open ValueDomainDerivation

module SignValueDomain : VALUE_DOMAIN = struct

    type t = Bottom | Z | N | P | Top

    let top = Top

    let bottom = Bottom

    let is_bottom s = s = Bottom

    let neg = function
        | N -> P
        | P -> N
        | s -> s

    let add s r =
        match s, r with
        | Bottom, _ | _, Bottom -> Bottom
        | Top, _ | _, Top -> Top
        | Z, v | v, Z -> v
        | P, P -> P
        | N, N -> N
        | _ -> Top

    let sub s r = add s (neg r)

    let mult s r =
        match s, r with
        | Bottom, _ | _, Bottom -> Bottom
        | Z, _ | _, Z -> Z
        | Top, _ | _, Top -> Top
        | P, v -> v
        | N, v -> neg v

    let div s r = if is_bottom r then Bottom else mult s r

    let const (z : Z.t) : t =
        match Z.sign z with
        | -1 -> N
        | 1 -> P
        | _ -> Z

    let rand (a : Z.t) (b : Z.t) : t =
        match Z.sign a, Z.sign b with
        | 0, 0 -> Z
        | -1, 1 | 1, -1 -> Top
        | 1, _ | _, 1 -> P
        | _ -> N

    let unary (s : t) iuop : t= Frontend.AbstractSyntax.(
        match iuop with
        | AST_UNARY_PLUS -> s
        | AST_UNARY_MINUS -> neg s
    )

    let binary (s : t) (r : t) ibop : t = Frontend.AbstractSyntax.(
        match ibop with
        | AST_PLUS -> add s r
        | AST_MINUS -> sub s r
        | AST_MULTIPLY -> mult s r
        | AST_DIVIDE -> div s r
        | AST_MODULO -> Top (* Check modulo behaviour *)
    )

    let compare (s : t) (r : t) cop : t * t = s, r (* TODO *)

    let bwd_unary (s : t) iuop (target : t) : t = s (* TODO *)

    let bwd_binary (s : t) (r : t) ibop (target : t) : t * t = s, r (* TODO *)

    let join (s : t) (r : t) : t =
        match s, r with
        | Bottom, v | v, Bottom -> v
        | Z, v | v, Z -> v
        | Top, _ | _, Top -> Top
        | _ -> if s = r then s else Top

    let meet (s : t) (r : t) : t =
        match s, r with
        | Bottom, _ | _, Bottom -> Bottom
        | Top, v | v, Top -> v
        | _ -> if s = r then s else Z

    let widen : t -> t -> t = join

    let narrow : t -> t -> t = meet

    let leq (s : t) (r : t) : bool =
        match s, r with
        | Bottom, _ | _, Top -> true
        | Top, _ | _, Bottom -> false
        | Z, _ -> true
        | _ -> s = r

    let pp (formatter : Format.formatter) (s : t) : unit =
        Format.pp_print_string formatter (
            match s with
            | Bottom -> "bottom"
            | Z -> "=0"
            | N -> "<=0"
            | P -> ">=0"
            | Top -> "top"
        )

end


module SignDomain(Vars : VARS) : DOMAIN =
    ValueDomainDerivation(SignValueDomain)(Vars)

