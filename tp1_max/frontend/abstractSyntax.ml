(*
  Cours "Sémantique et Application à la Vérification de programmes"
  
  Charles de Haro 2025
  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

(* 
  Definition of the abstract syntax trees output by the parser.
*)

(* position in the source file, we use ocamllex's default type *)

type position = Lexing.position

let position_unknown = Lexing.dummy_pos

(* extents are pairs of positions *)

type extent = position * position (* start/end *)

let extent_unknown = (position_unknown, position_unknown)

(* Many parts of the syntax are tagged with an extent indicating which
   part of the parser-file corresponds to the sub-tree.
   This is very useful for interesting error reporting!
 *)
type 'a ext = 'a * extent

(* variable identifiers, just strings for now *)
(* local variables and scoping would require using UNIQUE IDENTIFIERS
   to handle the case where several variables have the same name
 *)
type id = Id of string

(* constants *)
type const =
  | Ebool of bool (* boolean constants *)
  | Eint of Z.t (* unbounded integer contants *)

(* unary expression operators *)
type unop =
  (* arithmetic operators *)
  | Eplus (* +e *)
  | Eminus (* -e *)
  (* logical operators *)
  | Enot (* !e logical negation *)

(* binary expression operators *)
type binop =
  (* arithmetic operators, work only for int *)
  | Eadd (* e + e *)
  | Esub (* e - e *)
  | Emultiply (* e * e *)
  | Edivide (* e / e *)
  | Emodulo (* e % e *)
  (* polymorphic comparison, should work for int and bool *)
  | Eequal (* e == e *)
  | Enequal (* e != e *)
  (* arithmetic comparisons, work only for int *)
  | Elt (* e < e *)
  | Ele (* e <= e *)
  | Egt (* e > e *)
  | Ege (* e >= e *)
  (* boolean operators, work only for bool *)
  | Eand (* e && e *)
  | Eor (* e || e *)

(* expressions *)
type expr =
  (* unary operation *)
  | Eunop of unop * expr ext
  (* binary operation *)
  | Ebinop of binop * expr ext * expr ext
  (* variable use *)
  | Eid of id ext
  (* constants *)
  | Econst of const ext
  (* non-deterministic choice between two integers *)
  (* both bounds are inclusive *)
  | Erand of Z.t ext * Z.t ext

(* left part of assignments *)
type lvalue = Var of id

(* statements *)
type stmt =
  (* block of statements { ... } *)
  | Sblock of stmt ext list
  (* assignment  lvalue = expr *)
  | Sassign of lvalue ext * expr ext
  (* if-then-else; the else branch is optional *)
  | Sif of
      expr ext (* condition *) * stmt ext (* then branch *) * stmt ext option
  (* optional else *)
  (* while loop *)
  | Swhile of expr ext (* condition *) * stmt ext (* body *)
  (* exits the program *)
  | Shalt
  (* assertion: fail if the boolean expression does not hold *)
  | Sassert of expr ext
  (* prints the value of some variables *)
  | Sprint of lvalue ext list

(* top-level statements *)
type toplevel = (* statement to execute *)
  | Tstmt of stmt ext

(* a program is a list of top-level statements *)
type prog = toplevel list ext
