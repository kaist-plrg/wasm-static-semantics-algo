open Targets_wasm.Wasm

module Cli_task : Cli.Command.CLI_TASK with type input = Typecheck.input =
struct
  include Typecheck

  let cli_flags =
    let open Core.Command.Let_syntax in
    let open Core.Command.Param in
    let%map filename = flag "-p" (required string) ~doc:"FILE Wasm file to process" in
    make ~filename ()
end

let command = Cli.Command.make ~summary:"Run Wasm typechecker" (module Cli_task)

