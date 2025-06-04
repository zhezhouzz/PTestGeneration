type mode = Debug | Release [@@deriving yojson]

type preload_path = {
  predefined_path : string;
  axioms_path : string;
  templates_path : string;
  p_header_template_path : string;
  p_client_template_path : string;
}
[@@deriving yojson]

type meta_config = {
  log_tags : string list;
  mode : mode;
  max_printing_size : int;
  prim_path : preload_path;
  prover_timeout_bound : int;
  bool_options : (string * bool) list;
}
[@@deriving yojson]

let normalize_config c =
  match c.mode with Release -> { c with log_tags = [] } | Debug -> c

let show_var_type_in_prop = "show_var_type_in_prop"
let instantiate_poly_type_var_in_smt = "instantiate_poly_type_var_in_smt"
let show_record_type_feilds = "show_record_type_feilds"

let default_bool_options =
  [
    (show_var_type_in_prop, false);
    (instantiate_poly_type_var_in_smt, false);
    (show_record_type_feilds, false);
  ]

let get_bool_option_by_name c name =
  match List.find_opt (fun x -> String.equal name (fst x)) c.bool_options with
  | Some b -> snd b
  | None -> (
      match
        List.find_opt (fun x -> String.equal name (fst x)) default_bool_options
      with
      | Some b -> snd b
      | None -> failwith (Printf.sprintf "cannot find option %s" name))
