type source_kind = Structure | Signature

val convert :
  ?conf:Ocamlformat_lib.Conf.t ->
  ?associative_operators:string list ->
  ?kind:source_kind ->
  ?input_name:string ->
  ?output_name:string ->
  string ->
  (string, string) result
(** [convert source] converts Reason implementations to MLX, or interfaces to
    OCaml when [kind] is [Signature]. It returns formatted source or a diagnostic.

    Configuration defaults to [Ocamlformat_lib.Conf.default]. Filenames are used
    only for diagnostics; this function does not read files, discover project
    configuration, write output, or exit the process. *)
