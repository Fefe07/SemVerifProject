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
        | _ -> (module IntervalDomain.Make(Vars)) (* default choice *)
    ) : Domain.DOMAIN) in

    let module Iter = Iterator.Make(AbsDom) in
    Iter.verbose := !Options.verbose;

    let result = Iter.iterate cfg in
    Iter.print_abs_nodemap result

(* parses arguments to get filename *)
let main () =
    let _ = Options.init () in
    doit !Options.file

let _ = main ()
