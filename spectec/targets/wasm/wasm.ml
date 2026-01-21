open Wasm_interpreter
open Source
open Construct

let spec_dir = "spec/static-sem-algo"
let test_base_dir = ""

let logging = ref false

let num_parse_fail = ref 0

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

  let make ?(expect = Runner.Task.Positive) ~filename () =
    { filename; expect }

  let collect ?dir () =
    let _ = dir in
    failwith "Wasm test collection not implemented"

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
      Ok ("Module_ok", List.map il_of_module wasts)
(*    | ".wat" ->
      let m, cs =
        filename
        |> parse_file filename Parse.Module.parse_file
        |> textual_to_module
      in
      let tmp = il_of_module m in
      Ok ("Module_ok", [ tmp ])
      (* TODO: Wasm ASTs to SpecTec IL values *)
*)
    | _ -> failwith "unsupported file extension"

  let source { filename; _ } = filename
  let expectation { expect; _ } = expect
  let format_output _values = "Typechecker succeeded"
  let save_output _filename _values = ()

end

