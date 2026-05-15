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

    let div s r = if r = Z then Bottom else mult s r

    let modulo s r = if r = Z then Bottom else s

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
        | AST_PLUS -> add
        | AST_MINUS -> sub
        | AST_MULTIPLY -> mult
        | AST_DIVIDE -> div
        | AST_MODULO -> modulo
    ) s r

    let leq (s : t) (r : t) : bool =
        match s, r with
        | Bottom, _ | _, Top -> true
        | Top, _ | _, Bottom -> false
        | Z, _ -> true
        | _ -> s = r

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

    let compare (s : t) (r : t) cop : t * t = Frontend.AbstractSyntax.(
        match cop with
        | AST_EQUAL ->
            if leq s r then s, s else if leq r s then r, r else Z, Z
        | AST_NOT_EQUAL ->
            if (s, r) = (Z, Z) then Bottom, Bottom else s, r
        | AST_LESS ->
            ( if r = Z || r = N then meet s N else s ),
            ( if s = Z || s = P then meet r P else r )
        | AST_LESS_EQUAL ->
            if (s, r) = (Z, Z) then Bottom, Bottom else
            ( if r = Z || r = N then meet s N else s),
            ( if s = Z || s = P then meet r P else r)
        | AST_GREATER ->
            ( if r = Z || r = P then meet s P else s),
            ( if s = Z || s = N then meet r N else r)
        | AST_GREATER_EQUAL ->
            if (s, r) = (Z, Z) then Bottom, Bottom else
            ( if r = Z || r = P then meet s P else s),
            ( if s = Z || s = N then meet r N else r)
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
            if s = Z || r = Z then
                let res = meet Z target in res, res
            else
            meet s (div target r), meet r (div target s)
        | AST_DIVIDE -> s, r (* Not implemented *)
        | AST_MODULO -> s, r (* Not implemented *)
    )

    let widen : t -> t -> t = join

    let narrow : t -> t -> t = meet

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

