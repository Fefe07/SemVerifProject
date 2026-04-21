(*
  Cours "Sémantique et Application à la Vérification de programmes"
  
  Charles de Haro 2025
  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

(* 
  Pretty-printer for abstract syntax trees.
*)

open AbstractSyntax
open Lexing

(* locations *)
(* ********* *)

let pp_position fmt p =
  Printf.fprintf fmt "%s:%i:%i" p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol)

let pp_extent fmt (p, q) =
  if p.pos_fname = q.pos_fname then
    if p.pos_lnum = q.pos_lnum then
      if p.pos_cnum = q.pos_cnum then
        Printf.fprintf fmt "%s:%i.%i" p.pos_fname p.pos_lnum
          (p.pos_cnum - p.pos_bol)
      else
        Printf.fprintf fmt "%s:%i.%i-%i" p.pos_fname p.pos_lnum
          (p.pos_cnum - p.pos_bol) (q.pos_cnum - q.pos_bol)
    else
      Printf.fprintf fmt "%s:%i.%i-%i.%i" p.pos_fname p.pos_lnum
        (p.pos_cnum - p.pos_bol) q.pos_lnum (q.pos_cnum - q.pos_bol)
  else
    Printf.fprintf fmt "%s:%i.%i-%s:%i.%i" p.pos_fname p.pos_lnum
      (p.pos_cnum - p.pos_bol) q.pos_fname q.pos_lnum (q.pos_cnum - q.pos_bol)

(* operators *)
(* ********* *)

let pp_unop fmt = function
  | Eplus ->
      Format.pp_print_string fmt "+"
  | Eminus ->
      Format.pp_print_string fmt "-"
  | Enot ->
      Format.pp_print_string fmt "!"

let pp_binop fmt = function
  | Emultiply ->
      Format.pp_print_string fmt "*"
  | Edivide ->
      Format.pp_print_string fmt "/"
  | Emodulo ->
      Format.pp_print_string fmt "%"
  | Eadd ->
      Format.pp_print_string fmt "+"
  | Esub ->
      Format.pp_print_string fmt "-"
  | Eequal ->
      Format.pp_print_string fmt "=="
  | Enequal ->
      Format.pp_print_string fmt "!="
  | Elt ->
      Format.pp_print_string fmt "<"
  | Ele ->
      Format.pp_print_string fmt "<="
  | Egt ->
      Format.pp_print_string fmt ">"
  | Ege ->
      Format.pp_print_string fmt ">="
  | Eand ->
      Format.pp_print_string fmt "&&"
  | Eor ->
      Format.pp_print_string fmt "||"

(* higher values mean higher precedence *)
let binary_precedence = function
  | Emultiply | Edivide | Emodulo ->
      6
  | Eadd | Esub ->
      5
  | Eequal | Enequal ->
      4
  | Elt | Ele | Egt | Ege ->
      3
  | Eand ->
      2
  | Eor ->
      1

(* precedence of the operator at the root of the expression;
   this is used to avoid printing unnecessary parentheses
 *)
let expr_precedence = function
  | Eunop (_, _) ->
      99
  | Ebinop (op, _, _) ->
      binary_precedence op
  | _ ->
      100

(* utility to print lists *)
let print_list f sep fmt l =
  let rec aux = function
    | [] ->
        ()
    | [a] ->
        f fmt a
    | a :: b ->
        f fmt a ;
        Format.pp_print_string fmt sep ;
        aux b
  in
  aux l

(* expressions *)
(* *********** *)

let pp_id fmt (Id v) = Format.pp_print_string fmt v

let pp_const fmt = function
  | Ebool b ->
      Format.pp_print_bool fmt b
  | Eint z ->
      Z.pp_print fmt z

let rec pp_expr fmt e =
  match e with
  | Eunop (op, (e1, _)) ->
      if expr_precedence e1 <= expr_precedence e then
        Format.fprintf fmt "%a (%a)" pp_unop op pp_expr e1
      else Format.fprintf fmt "%a %a" pp_unop op pp_expr e1
  | Ebinop (op, (e1, _), (e2, _)) ->
      Format.fprintf fmt "%a %a %a"
        ( if expr_precedence e1 <= expr_precedence e then fun fmt ->
            Format.fprintf fmt "(%a)" pp_expr
          else pp_expr )
        e1 pp_binop op
        ( if expr_precedence e2 <= expr_precedence e then fun fmt ->
            Format.fprintf fmt "(%a)" pp_expr
          else pp_expr )
        e2
  | Econst (c, _) ->
      pp_const fmt c
  | Erand ((i1, _), (i2, _)) ->
      Format.fprintf fmt "rand(%a, %a)" Z.pp_print i1 Z.pp_print i2
  | Eid (v, _) ->
      pp_id fmt v

let pp_lvalue fmt (Var v) = pp_id fmt v

(* statements *)
(* ********** *)

let rec pp_stmt fmt = function
  | Sblock b ->
      pp_block fmt b
  | Sassign ((v, _), (e, _)) ->
      Format.fprintf fmt "%a = @[<h0>%a;@]" pp_lvalue v pp_expr e
  | Sif ((e, _), (b1, _), None) ->
      Format.fprintf fmt "if (%a)@;  @[<v0>%a@]" pp_expr e pp_stmt b1
  | Sif ((e, _), (b1, _), Some (b2, _)) ->
      Format.fprintf fmt "if (%a)@;  @[<v0>%a@]@;else@;  @[<v0>%a@]" pp_expr e
        pp_stmt b1 pp_stmt b2
  | Swhile ((e, _), (b, _)) ->
      Format.fprintf fmt "while (%a)@;  @[<v0>%a@]" pp_expr e pp_stmt b
  | Sassert (e, _) ->
      Format.fprintf fmt "assert (%a);" pp_expr e
  | Sprint l ->
      Format.fprintf fmt "print (%a);"
        (Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ", ")
           pp_lvalue )
        (List.map fst l)
  | Shalt ->
      Format.pp_print_string fmt "halt;"

and pp_block fmt b =
  Format.fprintf fmt "{@;  @[<v0>%a@]@;}"
    (Format.pp_print_list ~pp_sep:Format.pp_print_cut (fun fmt (stmt, _) ->
         pp_stmt fmt stmt ) )
    b

let pp_toplevel fmt (Tstmt (stmt, _)) = pp_stmt fmt stmt

(* programs *)
(* ******** *)

let pp_prog fmt (p, _) =
  Format.fprintf fmt "@[<v0>%a@]@;"
    (Format.pp_print_list ~pp_sep:Format.pp_print_cut pp_toplevel)
    p
