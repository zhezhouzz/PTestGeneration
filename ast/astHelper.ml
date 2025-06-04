include Fv
include Map
include Subst
include Zutils
include Typectx
include Myconfig
open AutomataLibrary
include Prop
open ParseTree

let name_in_qvs name l = List.exists (fun x -> String.equal x.x name) l
let mk_pty name = Nt.Ty_constructor (name, [])
let p_machine_ty = mk_pty "machine"
let p_event_ty = mk_pty "event"
let p_string_ty = mk_pty "string"
let p_regex_ty = mk_pty "regex"
let mk_p_set_ty ty = Nt.Ty_constructor ("set", [ ty ])
let mk_p_seq_ty ty = Nt.Ty_constructor ("seq", [ ty ])
let mk_p_map_ty ty1 ty2 = Nt.Ty_constructor ("map", [ ty1; ty2 ])

let is_p_abstact_ty name = function
  | Nt.Ty_constructor (name', []) when String.equal name name' -> true
  | _ -> false

let is_empty_record_ty ty =
  match Nt.get_record_types ty with [] -> true | _ -> false

let layout_qv x = spf "(%s: %s)" x.x (Nt.layout x.ty)
let layout_qvs = split_by " " layout_qv
let p_prim_types = [ "int"; "bool"; "machine"; "any"; "string" ]

let rec is_p_prim_type = function
  | Nt.Ty_record { fds; _ } -> List.for_all (fun x -> is_p_prim_type x.ty) fds
  | Nt.Ty_tuple l -> List.for_all is_p_prim_type l
  | Nt.Ty_constructor (name, [])
    when List.exists (String.equal name) p_prim_types ->
      true
  | Nt.Ty_constructor (name, [ nt ]) ->
      (String.equal "set" name || String.equal "req" name) && is_p_prim_type nt
  | Nt.Ty_constructor (name, [ nt1; nt2 ]) ->
      String.equal "map" name && is_p_prim_type nt1 && is_p_prim_type nt2
  | _ -> false

let get_absty nt =
  let rec aux = function
    | Nt.Ty_record { fds; _ } -> List.concat_map (fun x -> aux x.ty) fds
    | Nt.Ty_tuple l -> List.concat_map aux l
    | Nt.Ty_constructor (name, [])
      when List.exists (String.equal name) p_prim_types ->
        []
    | Nt.Ty_constructor (name, []) -> [ name ]
    | Nt.Ty_constructor (_, [ nt ]) -> aux nt
    | Nt.Ty_constructor (_, [ nt1; nt2 ]) -> aux nt1 @ aux nt2
    | _ -> _die_with [%here] (Nt.layout nt)
  in
  Zdatatype.List.slow_rm_dup String.equal (aux nt)

open Zdatatype

let layout_trace_elem (op, args) =
  spf "%s(%s)" op (List.split_by_comma layout_constant args)

let layout_trace = List.split_by "; " layout_trace_elem
