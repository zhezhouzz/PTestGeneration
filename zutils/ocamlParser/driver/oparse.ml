let tool_name = "ocamlc"

let parse_imp_from_file ~sourcefile =
  let structure = Pparse.parse_implementation ~tool_name sourcefile in
  (* let _ = Printast.structure 0 Format.std_formatter structure in *)
  structure

let parse_imp str = Parse.implementation @@ Lexing.from_string str
let parse_core_type str = Parse.core_type @@ Lexing.from_string str
let parse_pattern str = Parse.pattern @@ Lexing.from_string str
let parse_expression str = Parse.expression @@ Lexing.from_string str

let layout_fmt fmtLayout t =
  let _ = Format.flush_str_formatter () in
  fmtLayout Format.str_formatter t;
  Format.flush_str_formatter ()

let string_of_expression = Pprintast.string_of_expression
let string_of_structure = Pprintast.string_of_structure
let string_of_core_type = layout_fmt Pprintast.core_type
let string_of_longident = layout_fmt Pprintast.longident
let string_of_pattern = layout_fmt Pprintast.pattern

(** Ast builder *)

open Parsetree

let desc_to_ct t =
  {
    ptyp_desc = t;
    ptyp_loc = Location.none;
    ptyp_loc_stack = [];
    ptyp_attributes = [];
  }
