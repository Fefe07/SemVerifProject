(*
  Cours "Sémantique et Application à la Vérification de programmes"

  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

open Frontend
open ControlFlowGraph
open Domains.Domain


module Make(Abs : DOMAIN) = struct
    (* cfg : cfg ; map : Abs.t NodeMap.t *)

    (* Printing *)
    let assert_log_formatter : Format.formatter ref = ref Format.std_formatter

    let print_assert_failure (pos : Lexing.position) =
        Format.fprintf !assert_log_formatter
            "File \"%s\", line %i: Assertion failure ...@."
            pos.pos_fname pos.pos_lnum


    let pp_abs_nodemap formatter (map : Abs.t NodeMap.t) : unit =
        let iter_node node abs : unit = Format.fprintf formatter "<%i>: %a@ "
            node.node_id
            Abs.pp abs
        in
        Format.fprintf formatter "Node Values:@   @[<v 0>";
        NodeMap.iter iter_node map;
        Format.fprintf formatter "@]"

    let print_abs_nodemap (map : Abs.t NodeMap.t) : unit =
        Format.printf "%a@." pp_abs_nodemap map

    let print_iter_state map set node abs new_abs =
        let pp_list = Format.pp_print_list
            ~pp_sep:(fun form () -> Format.fprintf form ",@ ")
            (fun form node -> Format.fprintf form "%i" node.node_id)
        in
        Format.printf"@[<v 2>IterstateSet :[[";
        Format.printf "@ Set:@[%a@] ;" pp_list (NodeSet.to_list set);
        Format.printf "@ Map:@[<v 0>%a@] ;" pp_abs_nodemap map;
        Format.printf "@ Node:%i ;" node.node_id;
        Format.printf "@ Abs:@[%a@] ;" Abs.pp abs;
        Format.printf "@ New Abs:@[%a@] ;" Abs.pp new_abs;
        Format.printf "@]@ ]]@."


    (* Graph analysis *)
    let init_nodes cfg = cfg.cfg_init_entry ::
        List.map (fun f -> f.func_entry) cfg.cfg_funcs


    let find_widening_points cfg : NodeSet.t =
        let rec search (seen : NodeSet.t) node : NodeSet.t =
            if NodeSet.mem node seen then NodeSet.singleton node else
            let new_seen = NodeSet.add node seen in
            node.node_out
                |> List.map (fun arc -> search new_seen arc.arc_dst)
                |> List.fold_left NodeSet.union NodeSet.empty
        in
        init_nodes cfg
            |> List.map (search NodeSet.empty)
            |> List.fold_left NodeSet.union NodeSet.empty



    (* Iterator *)
    let add_out_nodes node set = List.fold_left
        (fun set arc -> NodeSet.add (arc.arc_dst) set)
        set
        node.node_out

    let add_out_nodes_from_list nl set = List.fold_left
        (fun set node -> add_out_nodes node set) set nl

    let map_add_nodes_from_list nl abs map = List.fold_left
        (fun map node -> NodeMap.add node abs map)
        map
        nl


    let apply_instr (abs : Abs.t) inst : Abs.t =
        match inst with
        | CFG_skip _ -> abs
        | CFG_assign(var, iexpr) -> Abs.assign abs var iexpr
        | CFG_guard bexpr -> Abs.guard abs bexpr
        | CFG_assert((bexpr, (pos, _))) -> let open Frontend.AbstractSyntax in
            let nexpr = CFG_bool_unary (AST_NOT, bexpr) in
            let neg_abs = Abs.guard abs nexpr in
            let pos_abs = Abs.guard abs bexpr in
            if not (Abs.is_bottom neg_abs) then print_assert_failure pos;
            pos_abs
        | CFG_call _ -> abs (* TODO *)

    let update map node =
        node.node_in
            (* Getting all possible abstract domains for node *)
            |> List.map (fun arc ->
                    (apply_instr (NodeMap.find arc.arc_src map) arc.arc_inst)
                )
            (* Joining them *)
            |> List.fold_left Abs.join Abs.bottom



    let iterate cfg : Abs.t NodeMap.t =
        let wnodes = find_widening_points cfg in

        let rec iterate_rec cfg map set =
            if NodeSet.is_empty set then map else
            let node = NodeSet.choose set in
            let abs = NodeMap.find node map in
            let joined_abs = update map node in
            let new_abs =
                if NodeSet.mem node wnodes then Abs.widen abs joined_abs
                else joined_abs
            in
            print_iter_state map set node abs new_abs;
            if Abs.leq new_abs abs && Abs.leq abs new_abs then
                (* no update *)
                iterate_rec cfg map (NodeSet.remove node set)
            else
                let new_map = NodeMap.add node new_abs map in
                let new_set = set
                    |> NodeSet.remove node
                    |> add_out_nodes node
                in
                iterate_rec cfg new_map new_set
        in

        let init_nodes = init_nodes cfg in
        let map = NodeMap.empty
            |> map_add_nodes_from_list cfg.cfg_nodes Abs.bottom
            |> map_add_nodes_from_list init_nodes Abs.init
        in
        let set = add_out_nodes_from_list init_nodes NodeSet.empty in
        iterate_rec cfg map set

end

