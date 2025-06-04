open Ast

open Language
(** Build Types *)

let str_eq_to_bv y x = match x with Some x -> String.equal x y | None -> false
(* let vs_names n = List.init n (fun i -> spf "%s%i" "x_" i) *)

let _get_record_ty_fields loc ty =
  match ty with Nt.Ty_record l -> l | _ -> _failatwith loc "die"

let mk_p_abstract_ty name = Nt.Ty_constructor (name, [])
let mk_p_set_ty ty = Nt.Ty_constructor ("set", [ ty ])
let mk_p_seq_ty ty = Nt.Ty_constructor ("seq", [ ty ])
let mk_p_map_ty ty1 ty2 = Nt.Ty_constructor ("map", [ ty1; ty2 ])
let mk_p_event_ty = mk_p_abstract_ty "event"
let mk_p_ref_ty ty = Nt.Ty_constructor ("ref", [ ty ])
let mk_p_record_ty vs = Nt.Ty_record vs
let mk_p_string_ty = mk_p_abstract_ty "string"
let mk_p_regex_ty = mk_p_abstract_ty "regex"

let is_p_abstact_ty name = function
  | Nt.Ty_constructor (name', []) when String.equal name name' -> true
  | _ -> false

let mk_p_tuple_ty vs =
  Nt.Ty_record (List.mapi (fun i ty -> (string_of_int i)#:ty) vs)

let mk_p_machine_ty = mk_p_abstract_ty "machine"
let is_empty_record_ty = function Nt.Ty_record [] -> true | _ -> false

(** P Compiled File Convention *)
let p_response_actions_domain = "response_actions"#:(mk_p_set_ty mk_p_string_ty)

let lib_set_is_empty = "set_is_empty"#:Nt.bool_ty
let lib_intersection_set = "intersection_set"#:(mk_p_set_ty mk_p_string_ty)
let lib_set_union = "int_set_union"#:(mk_p_set_ty Nt.int_ty)
let server_domain_decl = "server_domain"#:(mk_p_seq_ty mk_p_machine_ty)

(* let machine_local_server_decl = "local_server" #: mk_p_machine_ty *)
let qtype_init_function_decl = "qtype_init"#:Nt.unit_ty
let state_decl = "state"#:Nt.int_ty
let gprop_id_decl = "gprop_id"#:Nt.int_ty
let default_world_name = "world"
let default_tmp_world_name = "tmp_world"
let world_to_gprop_id_function_decl = "world_to_gprop_id"#:Nt.int_ty
let action_name_mapping = "action_name"
let validate_function_decl op = (spf "validate_%s" op.x)#:Nt.bool_ty
let source_field_decl = "source"#:(mk_p_abstract_ty "machine")
let next_world_function op = spf "next_world_%s" op
let next_world_function_decl op = (next_world_function op.x)#:Nt.unit_ty
let action_domain_declar = "action_domain"#:(mk_p_set_ty mk_p_string_ty)
let action_domain_init_function_decl = "action_domain_init"#:Nt.unit_ty
let get_available_actions_function_name = "get_available_actions"
let global_event_name = "_global_"

let get_available_actions_function_decl =
  get_available_actions_function_name#:(mk_p_set_ty mk_p_string_ty)

let random_event_function_name op = spf "random_event_%s" op

let random_event_function_decl op =
  (random_event_function_name op.x)#:(Nt.mk_arr Nt.unit_ty op.ty)

let input_name = "input"
let check_final_function_name = "check_final"
let check_final_function_decl = check_final_function_name#:Nt.bool_ty
let loop_state_name = "Loop"
let init_state_name = "Init"
let error_state_name = "Error"
let instantiate_action_function_name op = spf "instantiate_action_%s" op.x

let realize_instantiated_action_function op =
  (spf "realize_instantiated_action_%s" op.x)#:Nt.unit_ty

let action_name_mapping_decl =
  action_name_mapping#:(mk_p_map_ty Nt.int_ty mk_p_string_ty)

(* the type of SFA's transitions *)
let raw_transition_type =
  mk_p_map_ty Nt.int_ty (* the state *)
    (mk_p_map_ty mk_p_string_ty (* the event name *)
       (mk_p_map_ty Nt.int_ty (* the prop index *)
          Nt.int_ty (* the next state *)))

let lib_seq_string_to_set = "seq_string_to_set"#:(mk_p_set_ty mk_p_string_ty)

(** P AST Builder *)

let mk_p_self = PThis#:mk_p_machine_ty
let mk_p_printf format es = (PPrintf (format, es))#:Nt.unit_ty
let mk_p_break = PBreak#:Nt.unit_ty
let mk_p_default nt = (PConst (PDefault nt))#:nt
let mk_pid id = (Pid id)#:id.ty
let mk_p_this = PThis#:Nt.unit_ty

let mk_p_ite condition tbranch fbranch =
  (PIf { condition; tbranch; fbranch })#:Nt.unit_ty

let mk_p_it condition tbranch =
  (PIf { condition; tbranch; fbranch = None })#:Nt.unit_ty

(* let mk_p_field_unsafe record field = (PField { record; field }) #: Nt.unit_ty
                                  *)

let mk_p_field record field =
  match record.ty with
  | Nt.Ty_record l -> (
      match List.find_opt (fun x -> String.equal x.x field) l with
      | None -> _die [%here]
      | Some x -> (PField { record; field })#:x.ty)
  | _ ->
      _die_with [%here]
        (spf "%s.%s has not a record type: %s"
           (layout_sexp_p_expr record.x)
           field (Nt.layout record.ty))

let mk_p_send dest event_name payload =
  (PSend { dest; event_name; payload })#:Nt.unit_ty

let mk_p_recv event_name input body =
  (PRecieve { event_name; input; body })#:Nt.unit_ty

(** TODO: record type and tuple type...*)
let mk_depair (record : (Nt.nt, Nt.nt p_expr) typed) =
  match record.ty with
  | Nt.Ty_tuple [ t1; t2 ] ->
      let fst = (PField { record; field = "0" })#:t1 in
      let snd = (PField { record; field = "1" })#:t2 in
      (fst, snd)
  | Nt.Ty_record [ x1; x2 ] ->
      let fst = (PField { record; field = "0" })#:x1.ty in
      let snd = (PField { record; field = "1" })#:x2.ty in
      (fst, snd)
  | _ -> _die_with [%here] (spf "die: %s" (Nt.layout record.ty))

let mk_field_nth record n =
  match record.ty with
  | Nt.Ty_record l -> (
      match List.nth_opt l n with
      | None -> _die [%here]
      | Some { x = field; ty } -> (PField { record; field })#:ty)
  | _ -> _die [%here]

let mk_p_app pfunc args =
  let _, retty = Nt.destruct_arr_tp pfunc.ty in
  (PApp { pfunc; args })#:retty

let mk_p_add_set e1 e2 =
  match e1.ty with
  | Nt.Ty_constructor ("set", [ t1 ]) ->
      if Nt.equal_nt t1 e2.ty then
        let f =
          "add_set"#:(Nt.construct_arr_tp ([ e1.ty; e2.ty ], Nt.unit_ty))
        in
        mk_p_app f [ e1; e2 ]
      else
        _die_with [%here]
          (spf "expect type %s but get type %s" (Nt.layout t1) (Nt.layout e2.ty))
  | _ -> _die [%here]

let mk_p_map_keys e1 =
  match e1.ty with
  | Nt.Ty_constructor ("map", [ t1; _ ]) ->
      let f = "keys"#:(Nt.mk_arr e1.ty (mk_p_set_ty t1)) in
      mk_p_app f [ e1 ]
  | _ -> _die [%here]

let mk_p_map_values e1 =
  match e1.ty with
  | Nt.Ty_constructor ("map", [ _; t2 ]) ->
      let f = "values"#:(Nt.mk_arr e1.ty (mk_p_set_ty t2)) in
      mk_p_app f [ e1 ]
  | _ -> _die [%here]

let mk_set_intersection e1 e2 =
  match e1.ty with
  | Nt.Ty_constructor ("set", [ _ ]) when Nt.equal_nt e1.ty e2.ty ->
      let f = "intersection"#:(Nt.construct_arr_tp ([ e1.ty; e1.ty ], e1.ty)) in
      mk_p_app f [ e1; e2 ]
  | _ -> _die [%here]

let mk_p_choose pexpr =
  match pexpr.ty with
  | Nt.Ty_constructor (name, [ nt ])
    when String.equal name "set" || String.equal name "seq" ->
      let pfunc = "choose"#:(Nt.mk_arr pexpr.ty nt) in
      mk_p_app pfunc [ pexpr ]
  | Nt.Ty_constructor (name, []) when String.equal name "int" ->
      let pfunc = "choose"#:(Nt.mk_arr Nt.int_ty Nt.int_ty) in
      mk_p_app pfunc [ pexpr ]
  | _ -> _die [%here]

open Zdatatype

let mk_p_seq rhs body = (PSeq { rhs; body })#:body.ty
let mk_p_seqs es e = List.fold_right mk_p_seq es e
let ( <++> ) = mk_p_seq

let mk_p_seqs_ es =
  match List.last_destruct_opt es with
  | None -> _die [%here]
  | Some (es, e) -> mk_p_seqs es e

let mk_p_assign (lvalue, rvalue) = (PAssign { lvalue; rvalue })#:Nt.unit_ty

let mk_p_vassign (lvalue, rvalue) =
  (PAssign { lvalue = mk_pid lvalue; rvalue })#:Nt.unit_ty

let mk_p_let lhs rhs body = (PLet { lhs; rhs; body })#:body.ty
let mk_p_return_void = (PReturn (PConst PUnit)#:Nt.unit_ty)#:Nt.unit_ty
let mk_p_int i = (PConst (PInt i))#:Nt.int_ty
let mk_p_bool b = (PConst (PBool b))#:Nt.bool_ty
let mk_p_string str = (PConst (PStr str))#:(mk_p_abstract_ty "string")
let mk_random_bool = (PConst PRandomBool)#:Nt.bool_ty

let mk_random_int =
  mk_p_app "choose"#:(Nt.mk_arr Nt.int_ty Nt.int_ty) [ mk_p_int 10000 ]

let mk_random_from_seq seq =
  match seq.ty with
  | Nt.Ty_constructor ("set", [ t2 ]) ->
      mk_p_app "choose"#:(Nt.mk_arr seq.ty t2) [ seq ]
  | _ -> _die_with [%here] (Nt.layout seq.ty)

let mk_random_from_enum l =
  mk_p_app
    "choose"#:(Nt.mk_arr Nt.int_ty Nt.int_ty)
    [ mk_p_int (List.length l) ]

let mk_p_access (container, index) =
  let e = PAccess { container; index } in
  let t2 =
    match container.ty with
    | Nt.Ty_constructor ("map", [ t1; t2 ]) ->
        if Nt.equal_nt t1 index.ty then t2
        else
          _die_with [%here] (spf "%s != %s" (Nt.layout t1) (Nt.layout index.ty))
    | Nt.Ty_constructor ("set", [ t2 ]) ->
        if Nt.equal_nt Nt.int_ty index.ty then t2
        else
          _die_with [%here]
            (spf "%s != %s" (Nt.layout Nt.int_ty) (Nt.layout index.ty))
    | Nt.Ty_constructor ("seq", [ t2 ]) ->
        (* HACK: server type = int *)
        if
          Nt.equal_nt Nt.int_ty index.ty
          || Nt.equal_nt (mk_p_abstract_ty "server") index.ty
        then t2
        else
          _die_with [%here]
            (spf "%s != %s" (Nt.layout Nt.int_ty) (Nt.layout index.ty))
    | _ ->
        _die_with [%here]
          (spf "%s[%s]?" (Nt.layout container.ty) (Nt.layout index.ty))
  in
  e#:t2

let mk_p_vaccess (container, index) = mk_p_access (mk_pid container, index)

let mk_foreach_map_with_key key map body =
  let value = mk_p_access (map, mk_pid key) in
  (ForeachMap { key; map; body = body value })#:Nt.unit_ty

let mk_foreach_map map body =
  match map.ty with
  | Nt.Ty_constructor ("map", [ t1; _ ]) ->
      let key = (Rename.unique "key")#:t1 in
      mk_foreach_map_with_key key map (body key)
  | _ -> _die [%here]

let mk_foreach_set set body =
  match set.ty with
  | Nt.Ty_constructor ("set", [ t ]) ->
      let elem = (Rename.unique "elem")#:t in
      (ForeachSet { elem; set; body = body (mk_pid elem) })#:Nt.unit_ty
  | _ -> _die [%here]

let mk_p_record l =
  let tys = List.map (fun (name, e) -> name#:e.ty) l in
  let ty = mk_p_record_ty tys in
  (PRecord l)#:ty

let mk_p_tuple l = mk_p_record @@ List.mapi (fun i e -> (string_of_int i, e)) l

let mk_p_return x =
  let rec aux x =
    match x.x with
    | PGoto _ -> x
    | PSeq { rhs; body } -> (PSeq { rhs; body = aux body })#:x.ty
    | PLet { lhs; rhs; body } -> (PLet { lhs; rhs; body = aux body })#:x.ty
    | _ -> (PReturn x)#:x.ty
  in
  aux x

let mk_p_halt = mk_p_return @@ ((PConst PHalt)#:Nt.unit_ty)

let mk_p_eq e1 e2 =
  if Nt.equal_nt e1.ty e2.ty then
    mk_p_app
      "=="#:(Nt.construct_arr_tp ([ e1.ty; e1.ty ], Nt.bool_ty))
      [ e1; e2 ]
  else _die [%here]

let mk_p_in e1 e2 =
  mk_p_app "in"#:(Nt.construct_arr_tp ([ e1.ty; e2.ty ], Nt.bool_ty)) [ e1; e2 ]

let mk_p_error = mk_p_return @@ ((PConst PError)#:Nt.unit_ty)
let mk_p_goto name = (PGoto name)#:Nt.unit_ty

let mk_p_or e1 e2 =
  mk_p_app
    "||"#:(Nt.construct_arr_tp ([ Nt.bool_ty; Nt.bool_ty ], Nt.bool_ty))
    [ e1; e2 ]

let mk_p_not a = mk_p_app "!"#:(Nt.mk_arr Nt.bool_ty Nt.bool_ty) [ a ]

let mk_p_ors l =
  match l with
  | [] -> mk_p_bool false
  | [ e ] -> e
  | e :: es -> List.fold_left mk_p_or e es

type pexpr = (Nt.nt, Nt.nt p_expr) typed

let init_p_int_map (m : (pexpr -> pexpr) IntMap.t) (expr : pexpr) =
  (* let () = *)
  (*   Printf.printf "%s: %s\n" (layout_p_expr 0 expr.x) (layout_pnt expr.ty) *)
  (* in *)
  let e1 = mk_p_assign (expr, mk_p_default expr.ty) in
  let es =
    IntMap.fold
      (fun i f res ->
        let lvalue = mk_p_access (expr, mk_p_int i) in
        f lvalue :: res)
      m []
  in
  match List.last_destruct_opt es with
  | None -> _die [%here]
  | Some (es, e') -> mk_p_seqs (e1 :: es) e'

let init_p_int64_map (m : (pexpr -> pexpr) StateMap.t) (expr : pexpr) =
  let e1 = mk_p_assign (expr, mk_p_default expr.ty) in
  let es =
    StateMap.fold
      (fun i f res ->
        let lvalue = mk_p_access (expr, mk_p_int i) in
        f lvalue :: res)
      m []
  in
  match List.last_destruct_opt es with
  | None -> _die [%here]
  | Some (es, e') -> mk_p_seqs (e1 :: es) e'

let init_p_str_map (m : (pexpr -> pexpr) StrMap.t) (expr : pexpr) =
  let e1 = mk_p_assign (expr, mk_p_default expr.ty) in
  let es =
    StrMap.fold
      (fun i f res ->
        let lvalue = mk_p_access (expr, mk_p_string i) in
        f lvalue :: res)
      m []
  in
  match List.last_destruct_opt es with
  | None -> _die [%here]
  | Some (es, e') -> mk_p_seqs (e1 :: es) e'

let p_expr_to_str expr =
  Sexplib.Sexp.to_string @@ sexp_of_p_expr (fun _ -> Sexplib.Sexp.unit) expr

let map_on_p_machine f items =
  List.map (function PMachine m -> PMachine (f m) | _ as item -> item) items

let mk_p_sizeof expr =
  let f = "sizeof"#:Nt.int_ty in
  match expr.ty with
  | Nt.Ty_constructor (name, _)
    when List.exists (String.equal name) [ "set"; "seq"; "map" ] ->
      mk_p_app f [ expr ]
  | _ -> _die_with [%here] (Nt.layout expr.ty)

let lift_bound_varaibles (expr : (Nt.t, Nt.t p_expr) typed) =
  let rec aux_ = function
    | PAssign { lvalue; _ } as expr ->
        let vars = match lvalue.x with Pid x -> [ x ] | _ -> [] in
        (vars, expr)
    | PLet { lhs; rhs; body } ->
        let l, body = aux body in
        (lhs :: l, PSeq { rhs = mk_p_vassign (lhs, rhs); body })
    | PSeq { rhs; body } ->
        let l1, rhs = aux rhs in
        let l2, body = aux body in
        (l1 @ l2, PSeq { rhs; body })
    | ForeachMap { key; body; map } ->
        let l, body = aux body in
        (key :: l, ForeachMap { key; body; map })
    | ForeachSet { elem; body; set } ->
        let l, body = aux body in
        (elem :: l, ForeachSet { elem; body; set })
    | PIf { tbranch; fbranch; condition } -> (
        let l1, tbranch = aux tbranch in
        match fbranch with
        | None -> (l1, PIf { tbranch; fbranch; condition })
        | Some fbranch ->
            let l2, fbranch = aux fbranch in
            (l1 @ l2, PIf { tbranch; fbranch = Some fbranch; condition }))
    | PRecieve { event_name; input; body } ->
        let l, body = aux body in
        (l, PRecieve { event_name; input; body })
    | PWhile { body } ->
        let l, body = aux body in
        (l, PWhile { body })
    | _ as e -> ([], e)
  and aux e =
    let l, e' = aux_ e.x in
    (l, e'#:e.ty)
  in
  aux expr

module TVSet = Rawdesym.TVSet

let mk_p_function_decl params local_vars body =
  let vars, body = lift_bound_varaibles body in
  let local_vars =
    List.slow_rm_dup (fun a b -> String.equal a.x b.x) (local_vars @ vars)
  in
  { params; local_vars; body }
