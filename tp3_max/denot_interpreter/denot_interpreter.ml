(*
  Cours "Sémantique et Application à la Vérification de programmes"
  
  Charles de Haro 2025
  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

(*
  Simple driver: parses the file given as argument and prints it back.

  You should modify this file to call your functions instead!
*)

open Frontend

(* parse and print filename *)
let doit filename =
    let prog = FileParser.parse_file filename in
    AbstractSyntaxPrinter.pp_prog Format.std_formatter prog


(* Deterministic semantics *)
open AbstractSyntax


type value =
    | Vbool of bool
    | Vint of Z.t

type value_err =
    | Val of value
    | Err of string


module Smap = Map.Make(struct
    type t = id
    let compare (Id a) (Id b) = String.compare a b
end)

type env = value Smap.t

type env_err =
    | Env of env
    | EnvErr of string

let error_mess (_ : extent) (message : string) =
    Format.sprintf "%s" message

let typeverif_bool ext = function
    | (Val (Vbool _)) as v -> v
    | Val _ -> Err (error_mess ext "Ceci n'est pas un booléen")
    | Err message -> Err message

let typeverif_int ext = function
    | (Val (Vint _)) as v -> v
    | Val _ -> Err (error_mess ext "Ceci n'est pas un entier")
    | Err message -> Err message




let rec eval_expr (environment : env) ((e, extent) : expr ext) = match e with
    | Econst (Ebool b, _) -> Val (Vbool b)
    | Econst (Eint k, _) -> Val (Vint k)

    | Eid (id, ext) -> begin try (
            Val (Smap.find id environment)
        ) with Not_found -> Err (error_mess ext "Variable non définie") end

    | Eunop (Eplus, (e', ext')) ->
        let e_rec = eval_expr environment (e',ext') in
        typeverif_int ext' e_rec
    | Eunop (Eminus, (e', ext')) ->
        let e_rec = eval_expr environment (e',ext') in
        begin match typeverif_int ext' e_rec with
        | Val (Vint k) -> Val (Vint (Z.neg k))
        | v -> v
        end
    | Eunop (Enot, (e', ext')) ->
        let e_rec = eval_expr environment (e', ext') in
        begin match typeverif_bool ext' e_rec with
        | Val (Vbool b) -> Val (Vbool (not b))
        | v -> v
        end

    | Ebinop (binop, e1, e2) ->
        let v1 = eval_expr environment e1
        and v2 = eval_expr environment e2 in
        eval_binop binop (v1, snd e1) (v2, snd e2)

    | Erand _ -> Err (error_mess extent "Random non introduit")


and eval_binop binop (v1, ext1) (v2,ext2) =
    match binop with
    (* Arithmetic args *)
    | Eadd | Esub | Emultiply | Edivide | Emodulo
    | Elt | Ele | Egt | Ege -> begin
        match typeverif_int ext1 v1, typeverif_int ext2 v2 with
        | Val (Vint k1), Val (Vint k2) -> begin
            match binop with
            | Eadd -> Val (Vint (Z.add k1 k2))
            | Esub -> Val (Vint (Z.sub k1 k2))
            | Emultiply -> Val (Vint (Z.mul k1 k2))
            | Edivide -> begin try Val (Vint (Z.div k1 k2))
                with Division_by_zero -> Err (error_mess ext2
                "Division by zero") end
            | Emodulo -> begin try Val (Vint (Z.rem k1 k2))
                with Division_by_zero -> Err (error_mess ext2
                "Module by zero") end
            | Elt -> Val (Vbool (Z.lt k1 k2))
            | Ele -> Val (Vbool (Z.leq k1 k2))
            | Egt -> Val (Vbool (Z.gt k1 k2))
            | Ege -> Val (Vbool (Z.geq k1 k2))
            | _ -> failwith "ne devrait pas être atteint"
        end
        | v, _ -> v
    end

    (* Boolean args *)
    | Eand | Eor -> begin
        match typeverif_bool ext1 v1 with
        | Val (Vbool b1) -> if (b1 = (binop = Eor)) then Val (Vbool b1) else
            typeverif_bool ext2 v2
        | v -> v
    end

    (* Polymorphic args *)
    | _ -> begin
        let rev = binop = Eequal in
        match v1, v2 with
        | Err m, _ | _, Err m -> Err m
        | Val (Vint k1), Val (Vint k2) -> Val (Vbool (rev = (Z.equal k1 k2)))
        | Val (Vbool b1), Val (Vbool b2) -> Val (Vbool (rev = (b1 = b2)))
        | Val (Vint _), _ -> Err (error_mess ext2 "Devrait être entier")
        | Val (Vbool _), _ -> Err (error_mess ext2 "Devrait être booléen")
    end

let rec eval_stmt environment (stmt, extent) =
    match environment with EnvErr m -> EnvErr m | Env env -> begin
    match stmt with
    | Sblock [] -> environment
    | Sblock (s::q) -> eval_stmt (eval_stmt environment s) (Sblock q, extent)
    | Sassign ((Var id, _), e) -> begin match eval_expr env e with
        | Val v -> Env (Smap.add id v env)
        | Err m -> EnvErr m
        end
    | Sif ((e, e_ext), s, None) -> begin
        match typeverif_bool e_ext (eval_expr env (e, e_ext)) with
        | Val (Vbool true) -> eval_stmt environment s
        | Val (Vbool false) -> environment
        | Err m -> EnvErr m
        | _ -> failwith "Ne devrait pas être atteint"
        end
    | Sif ((e, e_ext), s, (Some s2)) -> begin
        match typeverif_bool e_ext (eval_expr env (e, e_ext)) with
        | Val (Vbool true) -> eval_stmt environment s
        | Val (Vbool false) -> eval_stmt environment s2
        | Err m -> EnvErr m
        | _ -> failwith "Ne devrait pas être atteint"
        end
    | Swhile ((e, e_ext), s) -> begin
        match typeverif_bool e_ext (eval_expr env (e, e_ext)) with
        | Err m -> EnvErr m
        | Val (Vbool false) -> environment
        | Val (Vbool true) ->
            eval_stmt (eval_stmt environment s) (stmt, extent)
        | _ -> failwith "Ne devrait pas être atteint"
        end
    | Shalt -> environment
    | Sassert (e, e_ext) -> begin
        match typeverif_bool e_ext (eval_expr env (e, e_ext)) with
        | Err m -> EnvErr m
        | Val (Vbool false) -> EnvErr (error_mess extent "Assertion failed")
        | Val (Vbool true ) -> environment
        | _ -> failwith "Ne devrait pas être atteint"
        end
    | Sprint _ -> environment
    end

let eval_prog (prog, _) = List.fold_left (
        fun env (Tstmt s) -> eval_stmt env s
    ) (Env Smap.empty) prog



(* Env pretty printer *)

let pp_value formatter = function
    | Vint k -> Format.fprintf formatter "%s" @@ Z.to_string k
    | Vbool b -> Format.fprintf formatter "%s" @@ Bool.to_string b

let pp_env formatter = function
    | Env env ->
        Format.fprintf formatter "env : { @[\n";
        Smap.iter (fun (Id id) v ->
            Format.fprintf formatter "%s : %a\n" id pp_value v
        ) env;
        Format.fprintf formatter "@]}";
    | EnvErr m -> Format.fprintf formatter "%s" @@ m

let print_env = Format.printf "%a@." pp_env



(* ND interpreter *)

let value_compare v1 v2 = match v1, v2 with
    | Vbool b1, Vbool b2 -> Bool.compare b1 b2
    | Vbool _, _ -> -1
    | _, Vbool _ -> 1
    | Vint z1, Vint z2 -> Z.compare z1 z2


module VSet = Set.Make(struct
    type t = value_err
    let compare v1 v2 = match v1, v2 with
        | Err _, Err _ -> 0
        | Err _, _ -> -1
        | _, Err _ -> 1
        | Val v1, Val v2 -> value_compare v1 v2
end)

module ESet = Set.Make(struct
    type t = env_err
    let compare e1 e2 = match e1, e2 with
        | EnvErr _, EnvErr _ -> 0
        | _, EnvErr _ -> 1
        | EnvErr _, _ -> -1
        | Env env1, Env env2 -> Smap.compare value_compare env1 env2
end)


let get_interval z1 z2 =
    let rec cstr z =
        if Z.compare z z2 = 0 then 
            [Val (Vint (z))]
        else Val (Vint z) :: cstr (Z.succ z)
    in
    VSet.of_list (cstr z1)

let cross_map f vs1 vs2 =
    VSet.fold (fun v1 vs ->
        VSet.union vs (VSet.map (f v1) vs2)
    ) vs1 VSet.empty

let rec nd_eval_expr environment (e, extent) = match e with
    | Econst (Ebool b, _) -> VSet.singleton (Val (Vbool b))
    | Econst (Eint k, _) -> VSet.singleton (Val (Vint k))

    | Eid (id, ext) -> begin try (
            VSet.singleton (Val (Smap.find id environment))
        ) with Not_found -> 
            VSet.singleton (Err (error_mess ext "Variable non définie"))
        end

    | Eunop (Eplus, (e', ext')) ->
        let e_rec = nd_eval_expr environment (e',ext') in
        VSet.map (typeverif_int ext') e_rec
    | Eunop (Eminus, (e', ext')) ->
        let e_rec = nd_eval_expr environment (e',ext') in
        let tv e = begin match typeverif_int ext' e with
            | Val (Vint k) -> Val (Vint (Z.neg k))
            | v -> v
            end
        in VSet.map tv e_rec

    | Eunop (Enot, (e', ext')) ->
        let e_rec = nd_eval_expr environment (e', ext') in
        let tv e = begin match typeverif_bool ext' e with
            | Val (Vbool b) -> Val (Vbool (not b))
            | v -> v
            end
        in VSet.map tv e_rec

    | Ebinop (binop, e1, e2) ->
        let vs1 = nd_eval_expr environment e1 in
        let vs2 = nd_eval_expr environment e2 in
        let f v1 v2 = eval_binop binop (v1, snd e1) (v2, snd e2) in
        cross_map f vs1 vs2

    | Erand ((z1, _), (z2, _)) ->
        if Z.compare z1 z2 = 1 then
            VSet.singleton (Err (error_mess extent "Intervalle mal posée"))
        else
            get_interval z1 z2



let typeverif_bool_set ext = VSet.map (typeverif_bool ext)

let union_map_es_es f es =
    ESet.fold (fun env acc -> ESet.union acc (f env)) es ESet.empty

let map_vs_es f es =
    VSet.fold (fun v acc -> ESet.add (f v) acc) es ESet.empty


let extract_errors vs =
    VSet.fold (fun v es -> match v with
        | Err m -> ESet.add (EnvErr m) es
        | _ -> es
    ) vs ESet.empty

let filter bool envs e =
    let testenv enverr = match enverr with
        | Env env ->
            let vs = typeverif_bool_set (snd e) @@ nd_eval_expr env e in
            let incl = VSet.exists ((=) (Val (Vbool bool))) vs in
            if incl then ESet.add enverr (extract_errors vs)
            else extract_errors vs
        | EnvErr _ -> ESet.singleton (enverr)
    in
    union_map_es_es testenv envs

let rec fix f base =
    let next = f base in
    if base <> next then fix f next
    else base

let rec nd_eval_stmt_single environment (stmt, extent) =
    match environment with
    | EnvErr m -> ESet.singleton (EnvErr m)
    | Env env -> begin
    match stmt with
    | Sblock [] -> ESet.singleton environment
    | Sblock (s::q) ->
        nd_eval_stmt (nd_eval_stmt_single environment s) (Sblock q, extent)
    | Sassign ((Var id, _), e) ->
        let vs = nd_eval_expr env e in
        map_vs_es (function
                | Val v -> Env (Smap.add id v env)
                | Err m -> EnvErr m
            ) vs
    | Sif ((e, e_ext), s, None) ->
        let pos_envs = filter true (ESet.singleton environment) (e, e_ext) in
        let neg_envs = filter false (ESet.singleton environment) (e, e_ext) in
        ESet.union
            (nd_eval_stmt pos_envs s)
            neg_envs
    | Sif ((e, e_ext), s, (Some s2)) ->
        let pos_envs = filter true (ESet.singleton environment) (e, e_ext) in
        let neg_envs = filter false (ESet.singleton environment) (e, e_ext) in
        ESet.union
            (nd_eval_stmt pos_envs s)
            (nd_eval_stmt neg_envs s2)
    | Swhile ((e, e_ext), s) ->
        let f envs =
            let pos_envs = filter true envs (e, e_ext) in
            let neg_envs = filter false envs (e, e_ext) in
            ESet.union neg_envs (nd_eval_stmt pos_envs s)
        in
        fix f (ESet.singleton environment)

    | Shalt -> ESet.singleton environment
    | Sassert (e, e_ext) ->
        let vs = typeverif_bool_set e_ext (nd_eval_expr env (e, e_ext)) in
        map_vs_es
            (function
            | Val (Vbool false) -> EnvErr (error_mess extent "Assertion failed")
            | Val (Vbool true) -> environment
            | _ -> failwith "Ne devrait pas être atteint")
            vs
    | Sprint _ -> ESet.singleton environment
    end

and nd_eval_stmt envs stmt =
    union_map_es_es (fun env -> nd_eval_stmt_single env stmt) envs


let nd_eval_prog (prog, _) = List.fold_left (
        fun env (Tstmt s) -> nd_eval_stmt env s
    ) (ESet.singleton (Env Smap.empty)) prog



(* parses arguments to get filename *)
let main () =
    ignore (eval_prog);
    match Array.to_list Sys.argv with
    | _::filename::_ ->
        doit filename; Format.printf "\n@.";
        let prog = FileParser.parse_file filename in
        let env = nd_eval_prog prog in
        ESet.iter print_env env;
    | _ -> invalid_arg "no source file specified"

let _ = main ()

