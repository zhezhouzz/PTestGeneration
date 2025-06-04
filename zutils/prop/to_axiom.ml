open OcamlParser
open Oparse
open Parsetree
open Sugar
open To_prop

let axiom_of_item structure =
  match structure.pstr_desc with
  | Pstr_value (_, [ value_binding ]) -> (
      let name = To_id.typed_id_of_pattern value_binding.pvb_pat in
      let name, _ = (name.x, name.ty) in
      match value_binding.pvb_attributes with
      | [ x ] -> (
          match x.attr_name.txt with
          | "axiom" ->
              let tasks =
                match x.attr_payload with
                | PStr [] -> []
                | PPat (pat, None) -> To_id.tuple_id_of_pattern pat
                | _ -> _die [%here]
              in
              (name, tasks, prop_of_expr value_binding.pvb_expr)
          | _ ->
              _failatwith [%here]
                "syntax error: non known rty kind, not axiom | assert | library"
          )
      | _ -> _failatwith [%here] "wrong syntax")
  | _ ->
      let () = Printf.printf "%s\n" (string_of_structure [ structure ]) in
      _failatwith [%here] "translate not a func_decl"
