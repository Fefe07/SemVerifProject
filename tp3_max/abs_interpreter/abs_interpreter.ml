(* Abstract Interpretor : "Iterator" *)

open Frontend.AbstractSyntax
open Frontend.AbstractSyntaxPrinter

module type AbsType = sig
    type t
    val bottom : t
    val top : t

    val const_abs : Z.t -> t
    val interval : Z.t -> Z.t -> t

    val equal : t -> t -> bool
    val neg : t -> t
    val add : t -> t -> t
    val sub : t -> t -> t
    val mult : t -> t -> t
    val div : t -> t -> t
    val modulo : t -> t -> t

    val bas_leq : t -> t -> t * t
    val bas_lt : t -> t -> t * t
    val bas_geq: t -> t -> t * t
    val bas_gt : t -> t -> t * t

    val join : t -> t -> t
    val widen : t -> t -> t

    val pp : Format.formatter -> t -> unit
end

module type Iterator_t = sig
    type env
    val eval_prog : prog -> env
    val pp_env : Format.formatter -> env -> unit
end

module Iterator(Abs : AbsType) : Iterator_t = struct


(* Type definitions *)

type value =
    | Vbool of bool
    | Vint of Abs.t

module Idmap = Map.Make(struct
    type t = id
    let compare (Id a) (Id b) = String.compare a b
end)

type env = value Idmap.t


(* Helper functions *)


let inject_literal (e : expr ext) abs (env : env) : env = 
    (* Sets the variable corresponding to expression ext e 
       to the abstract value abs, if this variable exists *)
    match fst e with
    | Eid (id, _) -> Idmap.add id (Vint abs) env
    | Econst _ -> env
    | _ -> failwith "cannot inject expression"

let map2 f idmap1 idmap2 =
    (* *)
    let f_map id v = f v (Idmap.find id idmap2) in
    Idmap.mapi f_map idmap1

let val_join v1 v2 = match v1, v2 with
    | Vint a, Vint b -> Vint (Abs.join a b)
    | _ -> failwith "Incorrect args for val_join"

let val_widen v1 v2 = match v1, v2 with
    | Vint a, Vint b -> Vint (Abs.widen a b)
    | _ -> failwith "Incorrect args for val_widen"

let rec fp f x =
    let next = f x in if x <> next then fp f next else x


let pp_value formatter = function
    | Vint a -> Abs.pp formatter a
    | Vbool b -> Format.fprintf formatter "%s" @@ Bool.to_string b

let pp_env formatter env =
    Format.fprintf formatter "env : { @[\n";
    Idmap.iter (fun (Id id) v ->
        Format.fprintf formatter "%s : %a\n" id pp_value v
    ) env;
    Format.fprintf formatter "@]}@."



(* Iterators *)

let rec eval_expr (environment : env) ((e, _) : expr ext) =
    match e with
    | Econst (Ebool b, _) -> Vbool b
    | Econst (Eint k, _) -> Vint (Abs.const_abs k)

    | Eid (id, _) -> begin try (
            Idmap.find id environment
        ) with Not_found -> Vint Abs.bottom
        end

    | Eunop (unop, e') -> let a = eval_expr environment e' in
        begin match a, unop with
        | Vint i, Eplus -> Vint i
        | Vint i, Eminus -> Vint (Abs.neg i)
        | Vbool b, Enot -> Vbool (not b)
        | _ -> failwith "Unop appliqué au mauvais type"
        end

    | Ebinop (binop, e1, e2) ->
        let a1 = eval_expr environment e1
        and a2 = eval_expr environment e2 in
        begin match a1, a2, binop with
        (* Boolean operators *)
        | Vbool b1, Vbool b2, Eand ->
                Vbool (b1 && b2)
        | Vbool b1, Vbool b2, Eor ->
                Vbool (b1 || b2)

        (* Abstract operators *)
        | Vint i1, Vint i2, Eadd -> Vint (Abs.add i1 i2)
        | Vint i1, Vint i2, Esub -> Vint (Abs.sub i1 i2)
        | Vint i1, Vint i2, Emultiply -> Vint (Abs.mult i1 i2)
        | Vint i1, Vint i2, Edivide -> Vint (Abs.div i1 i2)
        | Vint i1, Vint i2, Emodulo -> Vint (Abs.modulo i1 i2)
        | Vint _, Vint _, Elt -> failwith "TODO : Elt"
        | Vint _, Vint _, Ele -> failwith "TDOD : Ele"
        | Vint _, Vint _, Egt -> failwith "TDOD : Egt"
        | Vint _, Vint _, Ege -> failwith "TDOD : Ege"

        (* Polymorphic operators *)
        (* Is this the good way to treat equality tests ? *)
        (* Here [1,2] = [1,2]... , which is problematic... *)
        (* TODO... *)
        
        | Vbool b1, Vbool b2, Eequal ->
                Vbool (Bool.equal b1 b2)
        | Vint i1, Vint i2, Eequal ->
                Vbool (Abs.equal i1 i2)
        | Vbool b1, Vbool b2, Enequal ->
                Vbool (not @@ Bool.equal b1 b2)
        | Vint i1, Vint i2, Enequal ->
                Vbool (not @@ Abs.equal i1 i2)
        | _, _, Eequal -> Vbool false
        | _, _, Enequal -> Vbool true


        | _ -> failwith "Binop appliqué aux mauvais types"
        end

    | Erand ((a,_), (b,_)) -> Vint (Abs.interval a b)


let eval_expr_unwrap env e = match eval_expr env e with
    | Vbool _ -> failwith "Failed abstract unwrap"
    | Vint i -> i


let rec eval_stmt env (stmt, extent) =
    match stmt with
    | Sblock [] -> env
    | Sblock (s::q) ->
        eval_stmt (eval_stmt env s) (Sblock q, extent)
    | Sassign ((Var id, _), e) ->
        Idmap.add id (eval_expr env e) env

    | Sif ((Ebinop(binop, e1, e2), _), s, opt_s) ->
        let a = eval_expr_unwrap env e1 in
        let b = eval_expr_unwrap env e2 in
        (* backward abtract values *)
        let pos_a, pos_b = begin match binop with
            | Ele -> Abs.bas_leq a b
            | Elt -> Abs.bas_lt a b
            | Ege -> Abs.bas_leq b a
            | Egt -> Abs.bas_lt b a
            | _ -> failwith "Test case not supported"
        end in
        let neg_a, neg_b = begin match binop with
            | Ele -> Abs.bas_lt b a
            | Elt -> Abs.bas_leq b a
            | Ege -> Abs.bas_lt a b
            | Egt -> Abs.bas_leq a b
            | _ -> failwith "Test case not supported"
        end in

        let pos_unused = (a <> Abs.bottom && pos_a = Abs.bottom)
                || (b <> Abs.bottom && pos_b = Abs.bottom)
        and neg_unused = (neg_a = Abs.bottom)
                || (neg_b = Abs.bottom)
        in

        (* Possible pos_env *)
        let pos_env_opt = (
            if pos_unused then None
            else
                let pos_start_env = env
                    |> inject_literal e1 pos_a
                    |> inject_literal e2 pos_b
                in
                Some(eval_stmt pos_start_env s)
        ) in

        (* Possible neg_env *)
        let neg_env_opt = (
            begin match opt_s with | None -> None | Some s ->
            if neg_unused then None
            else
                let neg_start_env = env
                    |> inject_literal e1 neg_a
                    |> inject_literal e2 neg_b
                in
                Some(eval_stmt neg_start_env s)

            end
        ) in

        begin match opt_s, pos_env_opt, neg_env_opt with
            | _, None, None -> env
            | _, Some pe, Some ne -> map2 val_join pe ne
            | _, Some pe, None ->
                if neg_unused then pe else map2 val_join pe env
            | _, None, Some ne -> ne
        end
    | Sif _ -> failwith "Test case not supported"

    | Swhile ((Ebinop(binop, e1, e2), _), s) ->

        (* backward abstract semantics *)
        let pos_bas, neg_bas = begin match binop with
            | Ele -> Abs.bas_leq, Abs.bas_gt
            | Elt -> Abs.bas_lt, Abs.bas_geq
            | Ege -> Abs.bas_geq, Abs.bas_lt
            | Egt -> Abs.bas_gt, Abs.bas_leq
            | _ -> failwith "Test case not supported"
        end in

        let f m =
            let a = eval_expr_unwrap m e1 in
            let b = eval_expr_unwrap m e2 in
            let pos_a, pos_b = pos_bas a b in
            (* start_env takes into account that test condition is verified *)
            let start_env = m
                |> inject_literal e1 pos_a
                |> inject_literal e2 pos_b
            in
            let end_env = eval_stmt start_env s in
            let nm = map2 val_widen m end_env in
            Printf.printf "Environment after one step of widening : \n";
            pp_env Format.std_formatter nm ;
(*
            Format.printf "a : %a; a_start : %a; a_end : %a; a_wide : %a@."
                Abs.pp a
                Abs.pp pos_a
                Abs.pp (eval_expr_unwrap end_env e1)
                Abs.pp (eval_expr_unwrap nm e1);
            Format.printf "b : %a; b_start : %a; b_end : %a; b_wide : %a@."
                Abs.pp b
                Abs.pp pos_b
                Abs.pp (eval_expr_unwrap end_env e2)
                Abs.pp (eval_expr_unwrap nm e2);
*)
            nm
        in
        
        let m_n = fp f env in
        Printf.printf "Final environment after widening : \n";
        pp_env Format.std_formatter m_n ;
        let a = eval_expr_unwrap m_n e1 in
        let b = eval_expr_unwrap m_n e2 in
        (* Negation of loop condition *)
        let pos_a, pos_b = neg_bas a b in
(*
        Format.printf "a_while : %a; a_out : %a@." Abs.pp a Abs.pp pos_a;
        Format.printf "b_while : %a; b_out : %a@." Abs.pp b Abs.pp pos_b;
*)
        m_n |> inject_literal e1 pos_a
            |> inject_literal e2 pos_b
    | Swhile _ -> failwith "Test case not supported"


    | Shalt | Sprint _ -> env
    (* | Sassert e -> 
        (* On ne traite que les cas où le programme termine sans erreur  -> on peut supposer le assert vrai *)
        match  *)

    | _ -> failwith "TODO eval_stmt"

(* Env pretty printer *)



let eval_prog (prog, _) = List.fold_left (
        fun env (Tstmt s) -> let env' = eval_stmt env s in  pp_stmt Format.std_formatter (fst s) ; Printf.printf "\n" ; pp_env Format.std_formatter env' ;  env'
    ) Idmap.empty prog




(* let print_env = Format.printf "%a@." pp_env *)


end
