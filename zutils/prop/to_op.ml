open Syntax
open Sugar

let string_to_op_opt str =
  if is_builtin_op str then Some (PrimOp str)
  else if is_dt_op str then Some (DtConstructor str)
  else None

let string_to_op str =
  match string_to_op_opt str with
  | Some op -> op
  | None -> _die_with [%here] "unknown operator of string"

let _string_to_dt_op loc str =
  match string_to_op str with
  | DtConstructor op -> DtConstructor op
  | _ -> _failatwith loc "is not data constructor"

let layout_op = function PrimOp str -> str | DtConstructor str -> str
