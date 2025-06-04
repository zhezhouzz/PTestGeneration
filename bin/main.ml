open Core
open Language
open Zutils

let regular_file =
  Command.Arg_type.create (fun filename ->
      match Sys_unix.is_file filename with
      | `Yes -> filename
      | `No -> failwith "Not a regular file"
      | `Unknown -> failwith "Could not determine if this was a regular file")

let test_parser source_file () =
  let ctx, code = Preprocess.preproress [ source_file ] in
  let () = Pp.printf "@{<bold>result:@}\n%s\n" (layout_p_items code) in
  ()

let print_source_code source_file dest () =
  let ctx, code = Preprocess.preproress [ source_file ] in
  let () = Pp.printf "@{<bold>result:@}\n%s\n" (layout_p_items code) in
  let _ = Codegen.compile ctx dest in
  ()

let rec read_all_p_files dir =
  (* Printf.printf "%s\n" dir; *)
  match Sys_unix.is_directory dir with
  | `Yes ->
      (* Printf.printf "dir: %s\n" dir; *)
      let files =
        List.map ~f:(Filename.concat dir)
        @@ List.of_array @@ Sys_unix.readdir dir
      in
      let res = List.concat_map ~f:read_all_p_files files in
      res
  | `No -> (
      (* Printf.printf "not a dir %s\n" dir; *)
      match Sys_unix.is_file dir with
      | `Yes ->
          (* Printf.printf "file: %s\n" dir; *)
          if Filename.check_suffix dir ".p" then [ dir ] else []
      | _ -> [])
  | `Unknown -> failwith "Could not determine if this was a dir"

let syn head_file source_file dest () =
  let ctx, code = Preprocess.preproress [ head_file; source_file ] in
  (* let ctx, code = Preprocess.preproress source_file in *)
  let () = Pp.printf "@{<bold>result:@}\n%s\n" (layout_p_items code) in
  let _ = Codegen.compile ctx dest in
  ()

(* let type_check source_file () = *)
(*   let code = Preprocess.preproress source_file in *)
(*   let () = Pp.printf "@{<bold>result:@} %s\n" (layout_structure code) in *)
(*   (\* let () = _die [%here] in *\) *)
(*   let _ = Typing.struc_check (Preprocess.load_bctx ()) code in *)
(*   () *)

let inv =
  "(starA (not (EGetClockBoundTimeNowReq (requester == lc)));\n\
  \   EGetClockBoundTimeNowReq (requester == lc);\n\
  \   starA (not (EGetClockBoundTimeNowReq (requester == lc))))\n\
  \  || starA (not (EGetClockBoundTimeNowReq (requester == lc)))"

let one_param_file message f =
  let cmd =
    Command.basic ~summary:message
      Command.Let_syntax.(
        let%map_open config_file =
          flag "config"
            (optional_with_default Myconfig.default_meta_config_path
               regular_file)
            ~doc:"config file path"
        and source_file = anon ("source_code_file" %: regular_file) in
        let () = Myconfig.meta_config_path := config_file in
        f source_file)
  in
  (message, cmd)

let two_param_file message f =
  let cmd =
    Command.basic ~summary:message
      Command.Let_syntax.(
        let%map_open config_file =
          flag "config"
            (optional_with_default Myconfig.default_meta_config_path
               regular_file)
            ~doc:"config file path"
        and source_file = anon ("source_code_file" %: regular_file)
        and output_file = anon ("output_code_file" %: string) in
        let () = Myconfig.meta_config_path := config_file in
        f source_file output_file)
  in
  (message, cmd)

let two_param_dir message f =
  let cmd =
    Command.basic ~summary:message
      Command.Let_syntax.(
        let%map_open config_file =
          flag "config"
            (optional_with_default Myconfig.default_meta_config_path
               regular_file)
            ~doc:"config file path"
        and source_file = anon ("source_code_file" %: string)
        and output_file = anon ("output_code_file" %: string) in
        let () = Myconfig.meta_config_path := config_file in
        f source_file output_file)
  in
  (message, cmd)

let three_param_dir message f =
  let cmd =
    Command.basic ~summary:message
      Command.Let_syntax.(
        let%map_open config_file =
          flag "config"
            (optional_with_default Myconfig.default_meta_config_path
               regular_file)
            ~doc:"config file path"
        and source_file1 = anon ("source_code_file" %: regular_file)
        and source_file2 = anon ("source_code_file" %: regular_file)
        and output_file = anon ("output_code_file" %: string) in
        let () = Myconfig.meta_config_path := config_file in
        f source_file1 source_file2 output_file)
  in
  (message, cmd)

let commands =
  Command.group ~summary:"Poirot"
    [
      two_param_file "print-source-code" print_source_code;
      three_param_dir "syn" syn;
    ]

let () = Command_unix.run commands
