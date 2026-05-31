open Domain
open Apron
module CFG = Frontend.ControlFlowGraph
module AS = Frontend.AbstractSyntax

module Make(Vars : VARS) : DOMAIN = struct

    (* Apron and Polka initializations *)
    type polyhedral = Polka.loose Polka.t

    let man : polyhedral Manager.t = Polka.manager_alloc_loose ()

    (* Variable environment, should not change *)
    let translate_var (var : CFG.var) : Var.t =
        let name = var.var_name ^ "(" ^ (Int.to_string var.var_id) ^ ")" in
        Var.of_string name

    let int_var_array : Var.t Array.t = Vars.support
        |> Array.of_list
        |> Array.map translate_var

    let env : Environment.t = Environment.make int_var_array [||]

    (* Translations from CFG to Apron *)
    let translate_int (z : Z.t) : Coeff.t =
        z |> Z.to_string |> Mpqf.of_string |> Coeff.s_of_mpqf

    let translate_rand (a : Z.t) (b : Z.t) : Coeff.t =
        let a' = a |> Z.to_string |> Mpqf.of_string in
        let b' = b |> Z.to_string |> Mpqf.of_string in
        Coeff.i_of_mpqf a' b'

    let translate_binop : AS.int_binary_op -> Texpr1.binop = function
        | AS.AST_PLUS -> Texpr1.Add
        | AS.AST_MINUS -> Texpr1.Sub
        | AS.AST_MULTIPLY -> Texpr1.Mul
        | AS.AST_DIVIDE -> Texpr1.Div
        | AS.AST_MODULO -> Texpr1.Mod

    let rec translate_iexpr (iexpr : CFG.int_expr) : Texpr1.expr =
        match iexpr with
        | CFG.CFG_int_const z -> Texpr1.Cst (translate_int z)
        | CFG.CFG_int_var var -> Texpr1.Var (translate_var var)
        | CFG.CFG_int_rand(a, b) -> Texpr1.Cst (translate_rand a b)
        | CFG.CFG_int_unary(AS.AST_UNARY_PLUS, e) ->
                translate_iexpr e
        | CFG.CFG_int_unary(AS.AST_UNARY_MINUS, e) -> let open Texpr1 in
                Unop(Neg, (translate_iexpr e), Int, Zero)
        | CFG.CFG_int_binary(ibop, e1, e2) ->
                let e1' = translate_iexpr e1 in
                let e2' = translate_iexpr e2 in
                let open Texpr1 in
                Binop(translate_binop ibop, e1', e2', Int, Zero)

    let translate_geq e1 e2 : Tcons1.t =
        let open Texpr1 in
        let e = of_expr env
            ( Binop(Sub, translate_iexpr e1, translate_iexpr e2, Int, Zero) )
        in
        Tcons1.make e Tcons1.SUPEQ

    let rec translate_constraint cop e1 e2 : Tcons1.earray =
        (* only straightforward translation of comparison constraints *)
        (* giving SUPEQ and EQ constraints *)
        let wrap1 c =
            let ar = Tcons1.array_make env 1 in
            Tcons1.array_set ar 0 c;
            ar
        in
        match cop with
        | AS.AST_LESS -> translate_constraint AS.AST_GREATER e2 e1
        | AS.AST_LESS_EQUAL -> translate_constraint AS.AST_GREATER_EQUAL e2 e1
        | AS.AST_GREATER ->
            let open CFG in
            let e2_incr =
                CFG_int_binary(AS.AST_PLUS, e2, CFG_int_const(Z.one))
            in
            let e1' = translate_iexpr e1 in
            let e2' = translate_iexpr e2_incr in
            let open Texpr1 in
            let e = of_expr env @@ Binop(Sub, e1', e2', Int, Zero) in
            let c = Tcons1.make e Tcons1.SUPEQ in
            wrap1 c
        | AS.AST_GREATER_EQUAL ->
            let e1' = translate_iexpr e1 in
            let e2' = translate_iexpr e2 in
            let open Texpr1 in
            let e = of_expr env @@ Binop(Sub, e1', e2', Int, Zero) in
            let c = Tcons1.make e Tcons1.SUPEQ in
            wrap1 c
        | AS.AST_EQUAL ->
            let e1' = translate_iexpr e1 in
            let e2' = translate_iexpr e2 in
            let open Texpr1 in
            let e = of_expr env @@ Binop(Sub, e1', e2', Int, Zero) in
            let c = Tcons1.make e Tcons1.EQ in
            wrap1 c
        | AS.AST_NOT_EQUAL ->
                failwith "Constraint translation"

    let negate_cop cop = AS.(
        match cop with
        | AST_EQUAL -> AST_NOT_EQUAL
        | AST_NOT_EQUAL -> AST_EQUAL
        | AST_LESS -> AST_GREATER_EQUAL
        | AST_LESS_EQUAL -> AST_GREATER
        | AST_GREATER -> AST_LESS_EQUAL
        | AST_GREATER_EQUAL -> AST_LESS
    )

    (* Domain *)
    type t = polyhedral Abstract1.t

    let init = Abstract1.of_box man env int_var_array
        (Array.make (Array.length int_var_array) (Interval.of_int 0 0))

    let bottom = Abstract1.bottom man env

    let assign abs var iexpr =
        Abstract1.assign_texpr man abs
            (translate_var var)
            (translate_iexpr iexpr |> Texpr1.of_expr env)
            None

    let bwd_assign abs var iexpr res = abs


    let join = Abstract1.join man
    let meet = Abstract1.meet man
    let widen = Abstract1.widening man
    let narrow = meet (* not well implemented *)
    let leq = Abstract1.is_leq man
    let is_bottom = Abstract1.is_bottom man

    let guard (abs : t) (bexpr : CFG.bool_expr) : t =
        (* bool handles the propagation of negation in the bool expression *)
        let rec guard_arg abs bool = function
            | CFG.CFG_bool_const b -> if b = bool then abs else bottom
            | CFG.CFG_bool_rand -> abs
            | CFG.CFG_compare(AS.AST_NOT_EQUAL as cop, e1, e2)
            | CFG.CFG_compare(AS.AST_EQUAL as cop, e1, e2) ->
                (* != is split into a join of two guards *)
                if bool = (cop = AS.AST_EQUAL) then
                    Abstract1.meet_tcons_array man abs
                        (translate_constraint AS.AST_EQUAL e1 e2)
                else
                    join (
                        Abstract1.meet_tcons_array man abs
                            (translate_constraint AS.AST_GREATER e1 e2)
                    ) (
                        Abstract1.meet_tcons_array man abs
                            (translate_constraint AS.AST_GREATER e2 e1)
                    )
            | CFG.CFG_compare(cop, e1, e2) ->
                let cop' = if bool then cop else negate_cop cop in
                Abstract1.meet_tcons_array man abs
                    (translate_constraint cop' e1 e2)
            | CFG.CFG_bool_unary(AS.AST_NOT, bexpr) ->
                    guard_arg abs (not bool) bexpr
            | CFG.CFG_bool_binary(AS.AST_AND as bbop, be1, be2)
            | CFG.CFG_bool_binary(AS.AST_OR as bbop, be1, be2) ->
                (* De Morgan laws propagate bool *)
                (if bool = (bbop = AS.AST_AND) then meet else join)
                    (guard_arg abs bool be1)
                    (guard_arg abs bool be2)
        in
        guard_arg abs true bexpr


    let pp = Abstract1.print

end

