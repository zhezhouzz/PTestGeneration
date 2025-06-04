open Ast
open OcamlParser
open Oparse
open Parsetree
open Zdatatype
open To_id

(* open To_op *)
open Sugar
open Mutils

let string_to_constant = function
  | "true" -> B true
  | "false" -> B false
  | "()" -> U
  | x -> failwith (spf "do not support literal: %s" x)

let expr_to_constant e =
  let mk_exn () =
    failwith
      (spf "do not support complicate literal: %s" (string_of_expression e))
  in
  match e.pexp_desc with
  (* | Pexp_tuple es -> Tu (List.map expr_to_constant es) *)
  | Pexp_construct (id, e) -> (
      let name = longid_to_id id in
      match e with None -> string_to_constant name | Some _ -> mk_exn ()
      (* ( *)
      (*   match (string_to_op name, expr_to_constant e) with *)
      (*   | DtConstructor op, Tu cargs -> Dt { constr = Nt.untyped op; cargs } *)
      (*   | _, _ -> mk_exn ()) *))
  | Pexp_constant (Pconst_integer (istr, None)) -> I (int_of_string istr)
  | Pexp_constant (Pconst_float (fstr, None)) -> F (float_of_string fstr)
  | Pexp_constant (Pconst_char c) -> C c
  | Pexp_constant (Pconst_string (str, _, _)) -> S str
  (* | Pexp_constant (Pconst_string (constr, _, _)) -> *)
  (*     Dt { constr = Nt.untyped constr; cargs = [] } *)
  (* | Pexp_array l -> SetLiteral (List.map expr_to_constant l) *)
  | _ -> mk_exn ()

let constant_to_expr v =
  let of_const c = desc_to_ocamlexpr (Pexp_constant c) in
  let aux v =
    match v with
    | U -> mk_construct ("()", [])
    | B true -> mk_construct ("true", [])
    | B false -> mk_construct ("false", [])
    | I i -> of_const (Pconst_integer (string_of_int i, None))
    | C char -> of_const (Pconst_char char)
    | S str -> of_const (Pconst_string (str, Location.none, None))
    | F float -> of_const (Pconst_float (string_of_float float, None))
  in
  aux v

let layout_constant v = string_of_expression @@ constant_to_expr v
let layout_constants ts = List.split_by_comma layout_constant ts
