open Frontend
open Abs_interpreter

module Int_iter = Iterator(Abs_int)


let main () =
    match Array.to_list Sys.argv with
    | _::filename::_ ->
            (* parse and print filename *)
            let prog = FileParser.parse_file filename in
            AbstractSyntaxPrinter.pp_prog Format.std_formatter prog;

            (* print env *)
            let final_env = Int_iter.eval_prog prog in
            Int_iter.pp_env Format.std_formatter final_env

    | _ -> invalid_arg "no source file specified"

let _ = main ()


