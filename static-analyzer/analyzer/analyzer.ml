(*
  Cours "Sémantique et Application à la Vérification de programmes"

  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

(*
  Simple driver: parses the file given as argument and prints it back.

  You should modify this file to call your functions instead!
*)

open Frontend
open Domains
open ControlFlowGraph

(* parse filename *)
let doit filename =
    let cfg = filename |> FileParser.parse_file |> Tree_to_cfg.prog in

    (* Verbose option : print cfg in stdout *)
    if !Options.verbose then
        Format.printf "%a" ControlFlowGraphPrinter.print_cfg cfg;

    (* print cfg in cfg.dot *)
    ControlFlowGraphPrinter.output_dot !Options.cfg_out cfg;

    let module Vars : Domain.VARS = struct let support = cfg.cfg_vars end in

    (* Using First Class Modules *)
    let module AbsDom = (val (
        match !Options.domain with
        | "sign" -> (module SignDomain.Make(Vars))
        | "interval" -> (module IntervalDomain.Make(Vars))
        | "congruence" -> (module CongruenceDomain.Make(Vars))
        | "polyhedral" -> (module PolyhedralDomain.Make(Vars))
        | "intervalcongruenceproduct" | "ICP" -> (module IntervalCongruenceProductDomain.Make(Vars))
        | _ -> (module IntervalDomain.Make(Vars)) (* default choice *)
    ) : Domain.DOMAIN) in

    
      (* Printf.printf("No backward\n"); *)
    let module Iter = Iterator.Make(AbsDom) in
    Iter.verbose := !Options.verbose;

    let result = Iter.iterate cfg in
    Iter.print_abs_nodemap result ;
    if !Options.backward then begin
      let module Iter_bwd = Iterator.BackwardMake(AbsDom) in
      Iter_bwd.verbose := !Options.verbose;
      (* bwd_iterate takes a starting node and a strating value *)
      (* Should we run the fwd analysis and then backward on assertions ? *)
      
      let a = List.find (fun (a:arc) -> match a.arc_inst with CFG_assert _ -> true | _ -> false) cfg.cfg_arcs in 
      (* let condition = match a.arc_inst with CFG_assert x -> x | _ -> assert(false) in   *)

      let n = a.arc_src in
      (* Negation de la condition du assert*)
      (* let abs = Abs.guard Abs.Top (not a.arc_inst) in *)

      let bwd_result = Iter_bwd.bwd_iterate cfg n (NodeMap.find n result) result in
      Iter_bwd.print_abs_nodemap bwd_result
    end


(* parses arguments to get filename *)
let main () =
    let _ = Options.init () in
    doit !Options.file

let _ = main ()
