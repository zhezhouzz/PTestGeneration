(* Define Parser related aux functions *)

val parse_imp_from_file : sourcefile:string -> Parsetree.structure
val parse_imp : string -> Parsetree.structure
val parse_core_type : string -> Parsetree.core_type
val parse_pattern : string -> Parsetree.pattern
val parse_expression : string -> Parsetree.expression
val layout_fmt : (Format.formatter -> 'a -> unit) -> 'a -> string
val string_of_expression : Parsetree.expression -> string
val string_of_structure : Parsetree.structure -> string
val string_of_core_type : Parsetree.core_type -> string
val string_of_longident : Longident.t -> string
val string_of_pattern : Parsetree.pattern -> string
val desc_to_ct : Parsetree.core_type_desc -> Parsetree.core_type
