open Cmdliner

let named = function Some "-" | None -> None | path -> path

let read_input input =
  match named input with
  | None -> In_channel.input_all stdin
  | Some path -> In_channel.with_open_bin path In_channel.input_all

let write_output output source =
  match named output with
  | None ->
      Out_channel.output_string stdout source;
      Out_channel.flush stdout
  | Some path ->
      Out_channel.with_open_bin path (fun channel ->
          Out_channel.output_string channel source)

let input_name input = Option.value (named input) ~default:"stdin.re"

let output_name input output =
  match named output with
  | Some path -> path
  | None ->
      let input = input_name input in
      let extension =
        if String.equal (Filename.extension input) ".rei" then ".mli"
        else ".mlx"
      in
      Filename.remove_extension input ^ extension

let source_kind input output =
  let has_extension extension path =
    Option.fold (named path) ~none:false ~some:(fun path ->
        String.equal (Filename.extension path) extension)
  in
  if has_extension ".rei" input || has_extension ".mli" output then Reason_to_mlx.Signature
  else Reason_to_mlx.Structure

let run associative_operators input output =
  try
    let source = read_input input in
    let input_name = input_name input in
    let output_name = output_name input output in
    let kind = source_kind input output in
    let is_stdin = Option.is_none (named input) in
    let conf =
      match
        Bin_conf.build_config ~enable_outside_detected_project:true ~root:None
          ~file:output_name ~is_stdin
      with
      | Ok conf -> conf
      | Error message -> failwith message
    in
    match
      Reason_to_mlx.convert ~conf ~associative_operators ~kind ~input_name
        ~output_name source
    with
    | Ok source ->
        write_output output source;
        `Ok ()
    | Error message -> `Error (false, message)
  with
  | Failure message | Sys_error message -> `Error (false, message)
  | exn -> `Error (false, Printexc.to_string exn)

let input =
  let doc = "Reason source file. Use - or omit it to read standard input." in
  Arg.(value & pos 0 (some string) None & info [] ~doc ~docv:"FILE")

let output =
  let doc =
    "Write MLX source to $(docv). Standard output is used when this option is \
     omitted."
  in
  Arg.(
    value & opt (some string) None & info [ "o"; "output" ] ~doc ~docv:"FILE")

let associative_operators =
  let doc =
    "Comma-separated infix operators that can be reassociated for flatter \
     output."
  in
  Arg.(
    value
    & opt (list string) []
    & info [ "associative-operators" ] ~doc ~docv:"OPERATORS")

let command =
  let doc = "convert Reason source to formatted MLX" in
  let info = Cmd.info "reason-to-mlx" ~doc in
  Cmd.v info
    Term.(
      ret (const run $ associative_operators $ input $ output))

let () = exit (Cmd.eval command)
