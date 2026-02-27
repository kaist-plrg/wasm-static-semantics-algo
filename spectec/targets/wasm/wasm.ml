open Wasm_interpreter
open Source
open Construct

let spec_dir = "spec/static-sem-algo"

let excludes_dir = ""

let test_base_dir = "test-sep/core"

let skip_dirs = [ "include" ]

let logging = ref false

let num_parse_fail = ref 0

let contains_substring s sub =
  try
    let _ = Str.search_forward (Str.regexp_string sub) s 0 in
    true
  with Not_found -> false

let collect_files_recursive ~suffix dir =
  let rec gather acc path =
    if Sys.file_exists path && Sys.is_directory path then (
      let entries = Sys.readdir path in
      Array.sort String.compare entries;
      Array.fold_left
        (fun acc name ->
          let full_path = Filename.concat path name in
          if List.mem name skip_dirs then acc else gather acc full_path)
        acc entries)
    else if Filename.check_suffix path suffix then path :: acc
    else acc
  in
  if Sys.file_exists dir then gather [] dir |> List.rev else []

let load_excludes dir =
  let exclude_files = collect_files_recursive ~suffix:".exclude" dir in
  List.concat_map
    (fun path ->
      let ic = open_in path in
      let rec read_lines acc =
        try
          let line = input_line ic |> String.trim in
          if String.length line = 0 || line.[0] = '#' then read_lines acc
          else read_lines (line :: acc)
        with End_of_file ->
          close_in ic;
          acc
      in
      read_lines [])
    exclude_files

let log fmt = Printf.(if !logging then fprintf stderr fmt else ifprintf stderr fmt)

let parse_file name parser_ file =
  Printf.printf "===== %s =====\n%!" name;
  log "===========================\n\n%s\n\n" name;

  try
    parser_ file
  with e ->
    let bt = Printexc.get_raw_backtrace () in
    print_endline ("- Failed to parse " ^ name ^ "\n");
    log ("- Failed to parse %s\n") name;
    num_parse_fail := !num_parse_fail + 1;
    Printexc.raise_with_backtrace e bt

let textual_to_module textual =
  match (snd textual).it with
  | Script.Textual (m, cs) -> (m, cs)
  | _ -> assert false

let is_excluded excludes path =
  List.exists (fun pattern -> contains_substring path pattern) excludes

module Target : Runner.Target.S = struct
  let name = "wasm"
  let spec_dir = spec_dir
  let test_dir = test_base_dir
end

module Typecheck = struct
  let name = "typechecker"

  module Target = Target

  type input = {
    filename : string;
    expect : Runner.Task.expectation;
  }

  let make ~filename () =
    let cmd =
      filename
      |> parse_file filename Parse.Script.parse_file
      |> List.filter (fun cmd ->
          match cmd.it with
          | Script.Module _ -> true
          | Script.Assertion ass ->
            (match ass.it with
            | Script.AssertInvalid _ -> true
            | _ -> false)
          | _ -> false)
      |> List.hd
    in
    match cmd.it with
    | Script.Module _ -> { filename; expect = Runner.Task.Positive }
    | Script.Assertion _ -> { filename; expect = Runner.Task.Negative }
    | _ -> failwith "unexpected command type"

  let collect ?dir () =
    let test_dir = Option.value dir ~default:Target.test_dir in
    let excludes = load_excludes excludes_dir in
    collect_files_recursive ~suffix:".wast" test_dir
    |> List.filter (fun filename -> not (is_excluded excludes filename))
    |> List.map (fun filename ->
      let expect =
        if contains_substring filename "_neg" then Runner.Task.Negative
        else Runner.Task.Positive

      in { filename; expect })

  let parse ~spec:_ { filename; _ } =
    match Filename.extension filename with
    | ".wast" -> (* TODO *)
      let commands =
        filename
        |> parse_file filename Parse.Script.parse_file (* Script.script = command list *)
        |> List.filter (fun cmd ->
            match cmd.it with
            | Script.Module _ -> true
            | Script.Assertion ass ->
              (match ass.it with
              | Script.AssertInvalid _ -> true
              | _ -> false
              )
            | _ -> false)
      in
      (* TODO: Wasm ASTs to SpecTec IL values *)
      let (wasts, _) = List.map (fun cmd ->
          match cmd.it with
          | Script.Module (_, def) ->
            let m, cs = Run.run_definition def in
            (m, cs)
          | Script.Assertion ass ->
            (match ass.it with
            | Script.AssertInvalid (def, _) ->
              let m, cs = Run.run_definition def in
              (m, cs)
            | _ -> failwith "unsupported assertion type")
          | _ -> failwith "unsupported command type") commands
        |> List.split
      in
      let il_modules = il_of_list "module" il_of_module wasts in
      Ok ("Modules_ok", [ il_modules ])
    | _ -> failwith "unsupported file extension"

  let source { filename; _ } = filename
  let expectation { expect; _ } = expect
  let format_output _values = "Typechecker succeeded"
  let save_output _filename _values = ()

end
