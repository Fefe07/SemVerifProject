(* Functor for deriving abstract domains from value domains *)
(* Abstract environments are maps from variables to abstract integer sets *)
(* Used for the abstract domains : intervals, congruence *)

open Domain
open ValueDomain

open Frontend.ControlFlowGraph

module ValueDomainDerivation
        (Abs : VALUE_DOMAIN)
        (Vars : VARS)
        : DOMAIN =
struct

    (* Unused elements from the VALUE_DOMAIN Abs : top, bottom, is_bottom *)

    (* Private *)

    (* Change the mapped abstract value of a variable, collapsing to bottom *)
    let change_map (var : var) (abs : Abs.t) (dom : Abs.t VarMap.t) =
        if Abs.is_bottom abs then VarMap.empty else
        VarMap.add var abs dom

    (* Generate a map on `Vars.support` from a function *)
    let map_gen (f : var -> Abs.t) : Abs.t VarMap.t =
        List.fold_left
            (fun m v -> change_map v (f v) m)
            VarMap.empty
            Vars.support

    (* Extends a binary operation "point à point" to maps *)
    let extend_binop (binop : Abs.t -> Abs.t -> Abs.t) map1 map2=
        let f v = binop (VarMap.find v map1) (VarMap.find v map2) in
        map_gen f

    let rec evaluate_iexpr (dom : Abs.t VarMap.t) (iexpr : int_expr) : Abs.t =
        match iexpr with
        | CFG_int_unary(iuop, e') ->
                Abs.unary (evaluate_iexpr dom e') iuop
        | CFG_int_binary(ibop, e1, e2) ->
                Abs.binary (evaluate_iexpr dom e1) (evaluate_iexpr dom e2) ibop
        | CFG_int_var(v) ->
                VarMap.find v dom
        | CFG_int_const(z) ->
                Abs.const z
        | CFG_int_rand(z1, z2) ->
                Abs.rand z1 z2


    let negate_cop cop = Frontend.AbstractSyntax.(
        match cop with
        | AST_EQUAL -> AST_NOT_EQUAL
        | AST_NOT_EQUAL -> AST_EQUAL
        | AST_LESS -> AST_GREATER_EQUAL
        | AST_LESS_EQUAL -> AST_GREATER
        | AST_GREATER -> AST_LESS_EQUAL
        | AST_GREATER_EQUAL -> AST_LESS
    )


    (* Public *)

    type t = Abs.t VarMap.t

    let init =
        let f _ = Abs.const Z.zero in
        map_gen f

    let bottom = VarMap.empty

    let assign dom var iexpr =
        change_map var (evaluate_iexpr dom iexpr) dom

    let join = extend_binop Abs.join

    let meet = extend_binop Abs.meet

    let widen = extend_binop Abs.widen

    let narrow = extend_binop Abs.narrow

    let leq map1 map2 =
        let check v = Abs.leq (VarMap.find v map1) (VarMap.find v map2) in
        List.for_all check Vars.support

    let is_bottom = VarMap.is_empty

    let rec guard map =

        (* Backwards variant of evaluate_iexpr *)
        (* Recursively calls the `bwd_<op>` functions to retrieve the domain
           that respects the given constraint *)
        (* Note : meets are done naïvely with domain `meet`, all the variables
           are checked every time *)
        let rec bwd_evaluate_iexpr iexpr abs dom =
            match iexpr with
            | CFG_int_unary(iuop, e') ->
                let a' = Abs.bwd_unary (evaluate_iexpr dom e') iuop abs in
                bwd_evaluate_iexpr e' a' dom
            | CFG_int_binary(ibop, e1, e2) ->
                let a1 = evaluate_iexpr dom e1 in
                let a2 = evaluate_iexpr dom e2 in
                let b1, b2 = Abs.bwd_binary a1 a2 ibop abs in
                meet
                    (bwd_evaluate_iexpr e1 b1 dom)
                    (bwd_evaluate_iexpr e2 b2 dom)
            | CFG_int_var(v) ->
                dom |> change_map v abs
            | CFG_int_const _
            | CFG_int_rand _ -> dom
        in

        (* Domain `guard`, but with a carried boolean argument, in order to
           propagate negation *)
        let rec guard_arg map bool = function
            | CFG_bool_unary(AST_NOT, bexpr) ->
                guard_arg map (not bool) bexpr
            | CFG_bool_binary(AST_AND, bexpr1, bexpr2) ->
                let merge_op = if bool then meet else join in
                merge_op (guard_arg map bool bexpr1) (guard_arg map bool bexpr2)
            | CFG_bool_binary(AST_OR, bexpr1, bexpr2) ->
                let merge_op = if bool then join else meet in
                merge_op (guard_arg map bool bexpr1) (guard_arg map bool bexpr2)
            | CFG_compare(cop, iexpr1, iexpr2) ->
                let x = evaluate_iexpr map iexpr1 in
                let y = evaluate_iexpr map iexpr2 in
                let x', y' =
                    Abs.compare x y (if bool then cop else negate_cop cop)
                in
                meet
                    (bwd_evaluate_iexpr iexpr1 x' map)
                    (bwd_evaluate_iexpr iexpr2 y' map)
            | CFG_bool_const(b) -> if b then map else VarMap.empty
            | CFG_bool_rand -> map
        in

        guard_arg map true


    let pp formatter map =
        Format.fprintf formatter "@[{\n";
        VarMap.iter
            (fun v a ->
                Format.fprintf formatter "  %s : %a\n"
                    v.var_name Abs.pp a
            )
            map;
        Format.fprintf formatter "}@]"

end

