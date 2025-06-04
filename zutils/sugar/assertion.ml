open Lexing

let _check_arity loc a b =
  if List.length a != List.length b then
    failwith
      (Printf.sprintf "Arity check error on %s line %i" loc.pos_fname
         loc.pos_lnum)
  else ()

let _check_equality loc eq a b =
  if not @@ eq a b then
    failwith
      (Printf.sprintf "Equality check error on %s line %i" loc.pos_fname
         loc.pos_lnum)
  else a

let _safe_combine loc a b =
  let () = _check_arity loc a b in
  List.combine a b

let pos_to_string loc =
  Printf.sprintf "[file %s line %i]" loc.pos_fname loc.pos_lnum

let _failatwith loc str =
  failwith (Printf.sprintf "%s: %s" (pos_to_string loc) str)

let _assert loc str b =
  if b then ()
  else
    failwith
      (Printf.sprintf "%s: Assertion fail with %s" (pos_to_string loc) str)

let here_msg (location : Lexing.position) msg =
  Printf.sprintf "%s: %s" (pos_to_string location) msg

let _here (location : Lexing.position) = here_msg location "die"

let _die_with (location : Lexing.position) msg =
  failwith (here_msg location msg)

let _die (location : Lexing.position) = failwith (_here location)

let _force_some (location : Lexing.position) msg opt =
  match opt with Some res -> res | None -> _failatwith location msg
