open Ppxlib.Parsetree
open Ppxlib.Asttypes
type longident = Ppxlib.Longident.t = Lident of string | Ldot of longident * string | Lapply of longident * longident
module Mlx = Ocamlformat_lib
module Mlx_ast = Ocamlformat_parser_extended

let is_reason_only_attribute_name = function
  | "explicit_arity" | "implicit_arity" | "reason.openSyntaxNotation"
  | "reason.preserve_braces" | "reason.quoted_extension" | "reason.raw_literal"
    ->
      true
  | _ -> false

let is_ocaml_keyword = function
  | "and" | "as" | "assert" | "asr" | "begin" | "class" | "constraint" | "do"
  | "done" | "downto" | "effect" | "else" | "end" | "exception" | "external"
  | "false" | "for" | "fun" | "function" | "functor" | "if" | "in" | "include"
  | "inherit" | "initializer" | "land" | "lazy" | "let" | "lor" | "lsl" | "lsr"
  | "lxor" | "match" | "method" | "mod" | "module" | "mutable" | "new"
  | "nonrec" | "object" | "of" | "open" | "or" | "private" | "rec" | "sig"
  | "struct" | "then" | "to" | "true" | "try" | "type" | "val" | "virtual"
  | "when" | "while" | "with" ->
      true
  | _ -> false

let is_valid_identifier_shape name =
  let valid_first = function 'a' .. 'z' | '_' -> true | _ -> false in
  let valid_rest = function
    | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' -> true
    | _ -> false
  in
  String.length name > 0
  && valid_first name.[0]
  && String.for_all valid_rest name

let is_valid_value_name name =
  is_valid_identifier_shape name && not (is_ocaml_keyword name)

(* A keyword-only name like "to" needs no rename: `\#to` is the same
   identifier, so the field and any placeholder keep that spelling. *)
let is_keyword_only_invalid name =
  is_valid_identifier_shape name && is_ocaml_keyword name

let normalized_field_name name =
  let without_hyphens = String.split_on_char '-' name |> String.concat "" in
  let has_uppercase =
    String.exists (function 'A' .. 'Z' -> true | _ -> false) without_hyphens
  in
  let name =
    if String.contains name '-' then
      if has_uppercase then without_hyphens
      else String.map (function '-' -> '_' | char -> char) name
    else name
  in
  let name = String.uncapitalize_ascii name in
  let name = if is_ocaml_keyword name then name ^ "_" else name in
  if is_valid_value_name name then Some name else None

let escape_keyword name = if is_ocaml_keyword name then "\\#" ^ name else name

let is_eligible_uppercase_placeholder name =
  String.length name > 0
  && (match name.[0] with 'A' .. 'Z' -> true | _ -> false)
  && is_valid_value_name (String.uncapitalize_ascii name)

(* An uppercase ICU placeholder isn't a valid OCaml field, so both it and
   the matching JS key get lowercased. Plural branch text isn't a placeholder. *)
let intl_message_occurrences message =
  let is_word_char = function
    | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> true
    | _ -> false
  in
  let len = String.length message in
  let scan_word pos =
    let rec loop i = if i < len && is_word_char message.[i] then loop (i + 1) else i in
    let stop = loop pos in
    if stop > pos then Some (String.sub message pos (stop - pos), stop) else None
  in
  let has_literal_at pos literal =
    let l = String.length literal in
    pos + l <= len && String.equal (String.sub message pos l) literal
  in
  let rec loop i depth plural_depths acc =
    if i >= len then List.rev acc
    else
      match message.[i] with
      | '}' ->
          let plural_depths =
            match plural_depths with d :: rest when d = depth -> rest | _ -> plural_depths
          in
          loop (i + 1) (depth - 1) plural_depths acc
      | '{' when (match plural_depths with d :: _ -> d = depth | [] -> false) ->
          loop (i + 1) (depth + 1) plural_depths acc
      | '{' -> (
          match scan_word (i + 1) with
          | Some (name, after) when has_literal_at after ", plural," ->
              loop (after + 1) (depth + 1)
                ((depth + 1) :: plural_depths)
                ((name, i + 1, after) :: acc)
          | Some (name, after) when has_literal_at after "}" ->
              loop (after + 1) depth plural_depths ((name, i + 1, after) :: acc)
          | _ -> loop (i + 1) (depth + 1) plural_depths acc)
      | _ -> loop (i + 1) depth plural_depths acc
  in
  loop 0 0 [] []

let rewrite_intl_message ~eligible_names message =
  let edits =
    intl_message_occurrences message
    |> List.filter_map (fun (name, start_, end_) ->
        if List.mem name eligible_names then Some (start_, end_, String.uncapitalize_ascii name) else None)
  in
  let buffer = Buffer.create (String.length message) in
  let last =
    List.fold_left
      (fun pos (start_, end_, replacement) ->
        Buffer.add_string buffer (String.sub message pos (start_ - pos));
        Buffer.add_string buffer replacement;
        end_)
      0 edits
  in
  Buffer.add_string buffer (String.sub message last (String.length message - last));
  Buffer.contents buffer

(* [%intl ...] never consumes `@@` values, so only intl.s/intl.el matter.
   The message is the whole payload or a {msg; desc; maxLength}'s `msg`. *)
let map_intl_message f (payload : Ppxlib.Parsetree.expression) =
  let rewritten (text, loc, delim) =
    Pconst_string (f text, loc, delim)
  in
  match payload.pexp_desc with
  | Pexp_constant (Pconst_string (text, loc, delim)) ->
      { payload with pexp_desc = Pexp_constant (rewritten (text, loc, delim)) }
  | Pexp_record (fields, base) ->
      let fields =
        List.map
          (fun ((label : Ppxlib.Longident.t Location.loc), (value : Ppxlib.Parsetree.expression)) ->
            match (label.txt, value.pexp_desc) with
            | Lident "msg", Pexp_constant (Pconst_string (text, loc, delim)) ->
                (label, { value with pexp_desc = Pexp_constant (rewritten (text, loc, delim)) })
            | _ -> (label, value))
          fields
      in
      { payload with pexp_desc = Pexp_record (fields, base) }
  | _ -> payload

type intl_scope = {
  ext_eligible : (Location.t, string list) Hashtbl.t;
  record_eligible : (Location.t, string list) Hashtbl.t;
}

(* Merges curried params because the OCaml printer expects one multi-arg
   node. *)
let rec is_simple_argument (expression : Ppxlib.Parsetree.expression) =
  expression.pexp_attributes = []
  &&
  match expression.pexp_desc with
  | Pexp_ident _ | Pexp_constant _ | Pexp_function _
  | Pexp_construct (_, None)
  | Pexp_variant (_, None) ->
      true
  | Pexp_construct (_, Some argument) | Pexp_variant (_, Some argument) | Pexp_field (argument, _) ->
      is_simple_argument argument
  | Pexp_tuple elements -> List.for_all is_simple_argument elements
  | _ -> false

let is_placeholder (expression : Ppxlib.Parsetree.expression) =
  match expression.pexp_desc with
  | Pexp_ident { txt = Lident "__x"; _ } -> expression.pexp_attributes = []
  | _ -> false

let placeholder_count expression =
  (object
     inherit [int] Ppxlib.Ast_traverse.fold as super

     method! expression expression count =
       super#expression expression
         (if is_placeholder expression then count + 1 else count)
  end)
    #expression expression 0

(* Reason parses `x->f(a, _)` as `x |. (fun __x -> f a __x)`. *)
let inline_placeholder_pipe (expression : Ppxlib.Parsetree.expression) =
  match expression.pexp_desc with
  | Pexp_apply
      ( { pexp_desc = Pexp_ident { txt = Lident "|."; _ }; _ },
        [
          (Nolabel, subject);
          ( Nolabel,
            {
              pexp_desc =
                Pexp_function
                  ( [
                      {
                        pparam_desc =
                          Pparam_val
                            ( Nolabel,
                              None,
                              { ppat_desc = Ppat_var { txt = "__x"; _ }; ppat_attributes = []; _ } );
                        _;
                      };
                    ],
                    None,
                    Pfunction_body
                      ({ pexp_desc = Pexp_apply (callee, arguments); pexp_attributes = []; _ } as
                       call) );
              pexp_attributes = [];
              _;
            } );
        ] )
    when placeholder_count call = 1
         && List.exists (fun (_, argument) -> is_placeholder argument) arguments
         && (is_simple_argument subject
            || List.for_all
                 (fun (_, argument) -> is_placeholder argument || is_simple_argument argument)
                 arguments) ->
      let arguments =
        List.map
          (fun (label, argument) -> if is_placeholder argument then (label, subject) else (label, argument))
          arguments
      in
      { expression with pexp_desc = Pexp_apply (callee, arguments) }
  | _ -> expression

let normalize_reason_bridge ~input_name ~(scope : intl_scope) =
  let eligible_names_at table loc =
    try Hashtbl.find table loc with Not_found -> []
  in
  object
    inherit Ppxlib.Ast_traverse.map as super
    val mutable preserve_curried_arity = false

    method! arg_label =
      function
      | Nolabel -> Nolabel
      | Labelled name -> Labelled (escape_keyword name)
      | Optional name -> Optional (escape_keyword name)

    method! binding_op binding =
      let binding = super#binding_op binding in
      let op =
        match binding.pbop_op.txt with
        | "let.await" -> "let*"
        | "and.await" -> "and*"
        | op -> op
      in
      { binding with pbop_op = { binding.pbop_op with txt = op } }

    method! extension ((name, _) as extension) =
      let previous_preserve_curried_arity = preserve_curried_arity in
      preserve_curried_arity <-
        preserve_curried_arity || String.equal name.txt "melange_only";
      let extension = super#extension extension in
      preserve_curried_arity <- previous_preserve_curried_arity;
      extension

    method! object_field field =
      let field = super#object_field field in
      match field.pof_desc with
      | Otag (label, type_) ->
          {
            field with
            pof_desc =
              Otag ({ label with txt = escape_keyword label.txt }, type_);
          }
      | Oinherit _ -> field

    method! pattern pattern =
      let pattern = super#pattern pattern in
      match pattern.ppat_desc with
      | Ppat_var ({ txt = "let.await"; _ } as name) ->
          { pattern with ppat_desc = Ppat_var { name with txt = "let*" } }
      | Ppat_var ({ txt = "and.await"; _ } as name) ->
          { pattern with ppat_desc = Ppat_var { name with txt = "and*" } }
      | _ -> pattern

    method! attributes attributes =
      attributes
      |> List.filter (fun (attribute : Ppxlib.Parsetree.attribute) ->
          not (is_reason_only_attribute_name attribute.attr_name.txt))
      |> super#attributes

    method! expression (expression : Ppxlib.Parsetree.expression) =
      let expression = super#expression expression in
      let attributes = expression.pexp_attributes in
      let location_stack = expression.pexp_loc_stack in
      let expression =
        if preserve_curried_arity then expression
        else Ppxlib.Ast_builder.Default.coalesce_arity expression
      in
      let expression = inline_placeholder_pipe expression in
      let expression =
        match expression.pexp_desc with
        | Pexp_record (fields, base) ->
            let eligible_names = eligible_names_at scope.record_eligible expression.pexp_loc in
            let fields =
              List.map
                (fun
                     ( (label : Ppxlib.Longident.t Location.loc),
                       (value : Ppxlib.Parsetree.expression) ) ->
                  match label.txt with
                  | Lident name
                    when is_eligible_uppercase_placeholder name
                         && List.mem name eligible_names ->
                      ({ label with txt = Lident (String.uncapitalize_ascii name) }, value)
                  | Lident name when is_keyword_only_invalid name ->
                      ( { label with txt = Lident (escape_keyword name) },
                        value )
                  | Lident name
                    when not (is_valid_value_name name) ->
                      let field_name =
                        match normalized_field_name name with
                        | Some name -> name
                        | None ->
                            failwith
                              (Printf.sprintf
                                 "%s:%d: object key \"%s\" has no valid OCaml field name"
                                 input_name label.loc.loc_start.pos_lnum name)
                      in
                      let loc = value.pexp_loc in
                      let attribute =
                        Ppxlib.Ast_helper.Attr.mk { txt = "mel.as"; loc }
                          (PStr
                             [
                               Ppxlib.Ast_helper.Str.eval
                                 (Ppxlib.Ast_helper.Exp.constant
                                    (Pconst_string (name, loc, None)));
                             ])
                      in
                      ( { label with txt = Lident field_name },
                        {
                          value with
                          pexp_attributes = attribute :: value.pexp_attributes;
                        } )
                  | Lident _ | Ldot _
                  | Lapply _ ->
                      (label, value))
                fields
            in
            { expression with pexp_desc = Pexp_record (fields, base) }
        | Pexp_extension
            ( ({ txt = ("intl.s" | "intl.el"); _ } as ext_name),
              PStr [ ({ pstr_desc = Pstr_eval (payload, payload_attrs); _ } as item) ] ) ->
            let eligible_names = eligible_names_at scope.ext_eligible expression.pexp_loc in
            let payload = map_intl_message (rewrite_intl_message ~eligible_names) payload in
            {
              expression with
              pexp_desc =
                Pexp_extension
                  (ext_name, PStr [ { item with pstr_desc = Pstr_eval (payload, payload_attrs) } ]);
            }
        | _ -> expression
      in
      {
        expression with
        pexp_attributes = attributes;
        pexp_loc_stack = location_stack;
      }
  end

(* OCaml 5 reserves `effect`, which Reason accepts as an identifier; print
   it as `\#effect`. Constructors (`true`/`false`) are skipped. *)
let escape_longident = function
  | Lident name -> Lident (escape_keyword name)
  | Ldot (path, name) -> Ldot (path, escape_keyword name)
  | Lapply _ as longident -> longident

let escape_lid (lid : longident Location.loc) =
  { lid with txt = escape_longident lid.txt }

let escape_name (name : string Location.loc) =
  { name with txt = escape_keyword name.txt }

let escape_keyword_identifiers =
  object
    inherit Ppxlib.Ast_traverse.map as super

    method! expression expression =
      let expression = super#expression expression in
      let desc =
        match expression.pexp_desc with
        (* `a mod b` is Pexp_ident "mod" applied: the keyword is the operator. *)
        | Pexp_ident
            { txt = Lident ("mod" | "land" | "lor" | "lxor" | "lsl" | "lsr" | "asr" | "or"); _ }
          ->
            expression.pexp_desc
        | Pexp_ident lid -> Pexp_ident (escape_lid lid)
        | Pexp_field (obj, lid) -> Pexp_field (obj, escape_lid lid)
        | Pexp_setfield (obj, lid, value) ->
            Pexp_setfield (obj, escape_lid lid, value)
        | Pexp_send (obj, meth) -> Pexp_send (obj, escape_name meth)
        | desc -> desc
      in
      { expression with pexp_desc = desc }

    method! pattern pattern =
      let pattern = super#pattern pattern in
      let desc =
        match pattern.ppat_desc with
        | Ppat_var name -> Ppat_var (escape_name name)
        | Ppat_record (fields, closed) ->
            Ppat_record
              (List.map (fun (lid, pat) -> (escape_lid lid, pat)) fields, closed)
        | desc -> desc
      in
      { pattern with ppat_desc = desc }

    method! core_type core_type =
      let core_type = super#core_type core_type in
      let desc =
        match core_type.ptyp_desc with
        | Ptyp_var name -> Ptyp_var (escape_keyword name)
        | Ptyp_constr (lid, args) -> Ptyp_constr (escape_lid lid, args)
        | Ptyp_poly (vars, body) -> Ptyp_poly (List.map escape_name vars, body)
        | desc -> desc
      in
      { core_type with ptyp_desc = desc }

    method! type_declaration declaration =
      let declaration = super#type_declaration declaration in
      { declaration with ptype_name = escape_name declaration.ptype_name }

    method! label_declaration declaration =
      let declaration = super#label_declaration declaration in
      { declaration with pld_name = escape_name declaration.pld_name }

    method! value_description description =
      let description = super#value_description description in
      { description with pval_name = escape_name description.pval_name }
  end

let contains_crlf contents = String.includes ~affix:"\r\n" contents

let quoted_string_delimiter contents =
  let delimiter_is_safe delimiter =
    match String.split_on_char '|' contents with
    | [] | [ _ ] -> true
    | _ :: tails ->
        let terminator = delimiter ^ "}" in
        List.for_all
          (fun tail -> not (String.starts_with ~prefix:terminator tail))
          tails
  in
  let rec choose suffix =
    let delimiter =
      if suffix = 0 then "" else "mlx" ^ String.make (suffix - 1) 'x'
    in
    if delimiter_is_safe delimiter then delimiter else choose (suffix + 1)
  in
  choose 0

let preserve_multiline_string_syntax =
  object
    inherit Ppxlib.Ast_traverse.map as super

    method! expression (expression : Ppxlib.Parsetree.expression) =
      let expression = super#expression expression in
      match expression.pexp_desc with
      | Pexp_constant (Pconst_string (contents, location, None))
        when location.loc_start.pos_lnum < location.loc_end.pos_lnum
             && (not (contains_crlf contents))
             && List.exists
                  (fun (attribute : Ppxlib.Parsetree.attribute) ->
                    String.equal attribute.attr_name.txt "reason.raw_literal")
                  expression.pexp_attributes ->
          (* Check the source span, not the decoded value, for newlines. *)
          let delimiter = quoted_string_delimiter contents in
          {
            expression with
            pexp_desc =
              Pexp_constant (Pconst_string (contents, location, Some delimiter));
          }
      | _ -> expression
  end

(* Pprintast reprints a string literal via `%S`, which turns non-ASCII
   bytes into digit soup and collapses `\xNN`/`\u{...}` notation. *)
let double_octal_escape_backslashes raw =
  let buffer = Buffer.create (String.length raw) in
  let length = String.length raw in
  let rec go i =
    if i < length then
      if raw.[i] = '\\' && i + 1 < length then (
        if raw.[i + 1] = 'o' then Buffer.add_char buffer '\\';
        Buffer.add_char buffer raw.[i];
        Buffer.add_char buffer raw.[i + 1];
        go (i + 2))
      else (
        Buffer.add_char buffer raw.[i];
        go (i + 1))
  in
  go 0;
  Buffer.contents buffer

let raw_text_to_restore contents attributes =
  match Reason.Reason_attributes.extract_raw_literal attributes with
  | None, _ -> None
  | Some raw, _ ->
      if String.equal (Printf.sprintf "%S" contents) ("\"" ^ raw ^ "\"") then
        None
      else Some (double_octal_escape_backslashes raw)

let preserve_raw_string_literals () =
  object (self)
    inherit Ppxlib.Ast_traverse.map as super
    val mutable literals = []
    method literals = List.rev literals

    method private placeholder contents (location : Location.t) attributes =
      if location.loc_start.pos_lnum <> location.loc_end.pos_lnum then None
      else
        Option.map
          (fun raw ->
            let placeholder =
              Printf.sprintf "\x00reason_to_mlx.raw_string_%d\x00"
                (List.length literals)
            in
            literals <- (placeholder, raw) :: literals;
            placeholder)
          (raw_text_to_restore contents attributes)

    method! expression (expression : expression) =
      let expression = super#expression expression in
      match expression.pexp_desc with
      | Pexp_constant (Pconst_string (contents, location, None)) ->
          Option.fold ~none:expression
            ~some:(fun placeholder ->
              {
                expression with
                pexp_desc =
                  Pexp_constant (Pconst_string (placeholder, location, None));
              })
            (self#placeholder contents location expression.pexp_attributes)
      | _ -> expression

    method! pattern (pattern : pattern) =
      let pattern = super#pattern pattern in
      match pattern.ppat_desc with
      | Ppat_constant (Pconst_string (contents, location, None)) ->
          Option.fold ~none:pattern
            ~some:(fun placeholder ->
              {
                pattern with
                ppat_desc =
                  Ppat_constant (Pconst_string (placeholder, location, None));
              })
            (self#placeholder contents location pattern.ppat_attributes)
      | _ -> pattern
  end

type source_kind = Structure | Signature

type source_comment = { id : int; text : string; location : Location.t }

let blank_end text offset =
  Option.value ~default:(String.length text)
    (String.find_first_index (fun char -> not (Char.Ascii.is_white char)) ~start:offset text)

let blank_start text offset =
  if offset = 0 then 0
  else
    match
      String.find_last_index (fun char -> not (Char.Ascii.is_white char)) ~start:(offset - 1) text
    with
    | Some index -> index + 1
    | None -> 0

let offset_in_comment comments offset =
  List.exists
    (fun (comment : source_comment) ->
      comment.location.loc_start.pos_cnum <= offset
      && offset < comment.location.loc_end.pos_cnum)
    comments

let comment_after_blanks ~text ~comments offset =
  let start = blank_end text offset in
  ( start,
    List.find_opt
      (fun (comment : source_comment) ->
        comment.location.loc_start.pos_cnum = start)
      comments )

let rec skip_blank_and_comments ~text ~comments offset =
  if offset < 0 || offset >= String.length text then offset
  else
    match comment_after_blanks ~text ~comments offset with
    | _, Some comment ->
        skip_blank_and_comments ~text ~comments comment.location.loc_end.pos_cnum
    | start, None -> start

type parsed_source =
  | Implementation of Ppxlib.Parsetree.structure
  | Interface of Ppxlib.Parsetree.signature

let map_source mapper = function
  | Implementation ast -> Implementation (mapper#structure ast)
  | Interface ast -> Interface (mapper#signature ast)

let iter_source iterator = function
  | Implementation ast -> iterator#structure ast
  | Interface ast -> iterator#signature ast

let intl_message_names (payload : Ppxlib.Parsetree.expression) =
  let names = ref [] in
  ignore
    (map_intl_message
       (fun text ->
         names := List.map (fun (n, _, _) -> n) (intl_message_occurrences text) @ !names;
         text)
       payload);
  !names

(* rhs is the object an intl.s/el extension's `@@` reads. *)
type intl_site = {
  ext : Ppxlib.Parsetree.expression;
  rhs : Ppxlib.Parsetree.expression;
  message_names : string list;
}

let intl_site_of (expression : Ppxlib.Parsetree.expression) =
  match expression.pexp_desc with
  | Pexp_apply
      ( { pexp_desc = Pexp_ident { txt = Lident "@@"; _ }; _ },
        [ (Nolabel, ext); (Nolabel, rhs) ] ) -> (
      match ext.pexp_desc with
      | Pexp_extension
          ({ txt = "intl.s" | "intl.el"; _ }, PStr [ { pstr_desc = Pstr_eval (payload, _); _ } ]) ->
          Some { ext; rhs; message_names = intl_message_names payload }
      | _ -> None)
  | _ -> None

(* A quoted-key object literal parses as `[%mel.obj { ... }]`: the record
   sits one extension payload down from the `@@` right-hand side. *)
let unwrap_record (expression : Ppxlib.Parsetree.expression) =
  match expression.pexp_desc with
  | Pexp_extension (_, PStr [ { pstr_desc = Pstr_eval (inner, _); _ } ]) -> inner
  | _ -> expression

let record_keys (record : Ppxlib.Parsetree.expression) =
  match record.pexp_desc with
  | Pexp_record (fields, _) ->
      List.filter_map
        (fun ((label : Ppxlib.Longident.t Location.loc), _) ->
          match label.txt with Lident name -> Some name | _ -> None)
        fields
  | _ -> []

let eligible_keys_of record message_names =
  message_names
  |> List.filter (fun name ->
      is_eligible_uppercase_placeholder name && List.mem name (record_keys record))
  |> List.sort_uniq String.compare

(* Scopes a rename to the object a `[%intl.s/el ...] @@ obj` reads,
   inline or let-bound. *)
let collect_intl_scope ast : intl_scope =
  let sites = ref [] in
  let ident_total = Hashtbl.create 16 and ident_rhs = Hashtbl.create 16 in
  let bump table name =
    Hashtbl.replace table name (1 + try Hashtbl.find table name with Not_found -> 0)
  in
  let collector =
    object
      inherit Ppxlib.Ast_traverse.iter as super

      method! expression expression =
        (match intl_site_of expression with
        | Some site ->
            sites := site :: !sites;
            (match site.rhs.pexp_desc with
            | Pexp_ident { txt = Lident name; _ } -> bump ident_rhs name
            | _ -> ())
        | None -> (
            match expression.pexp_desc with
            | Pexp_ident { txt = Lident name; _ } -> bump ident_total name
            | _ -> ()));
        super#expression expression
    end
  in
  iter_source collector ast;
  let record_eligible = Hashtbl.create 16 and ext_eligible = Hashtbl.create 16 in
  List.iter
    (fun { ext; rhs; message_names } ->
      let record = unwrap_record rhs in
      match record.pexp_desc with
      | Pexp_record _ ->
          let names = eligible_keys_of record message_names in
          Hashtbl.replace record_eligible record.pexp_loc names;
          Hashtbl.replace ext_eligible ext.pexp_loc names
      | _ -> ())
    !sites;
  (* Equal use counts mean no other reference depends on this name's
     original key: every use is an intl `@@` right-hand side. *)
  let qualifies name = Hashtbl.find_opt ident_total name = Hashtbl.find_opt ident_rhs name in
  let named_message_names = Hashtbl.create 16 in
  List.iter
    (fun { rhs; message_names; _ } ->
      match rhs.pexp_desc with
      | Pexp_ident { txt = Lident name; _ } when qualifies name ->
          let previous = try Hashtbl.find named_message_names name with Not_found -> [] in
          Hashtbl.replace named_message_names name (message_names @ previous)
      | _ -> ())
    !sites;
  let named_final = Hashtbl.create 16 in
  let find_named_record =
    object
      inherit Ppxlib.Ast_traverse.iter as super

      method! value_binding binding =
        (match binding.pvb_pat.ppat_desc with
        | Ppat_var { txt = name; _ } -> (
            match Hashtbl.find_opt named_message_names name with
            | Some message_names ->
                let record = unwrap_record binding.pvb_expr in
                let names = eligible_keys_of record message_names in
                Hashtbl.replace record_eligible record.pexp_loc names;
                Hashtbl.replace named_final name names
            | None -> ())
        | _ -> ());
        super#value_binding binding
    end
  in
  iter_source find_named_record ast;
  List.iter
    (fun { ext; rhs; _ } ->
      match rhs.pexp_desc with
      | Pexp_ident { txt = Lident name; _ } -> (
          match Hashtbl.find_opt named_final name with
          | Some names -> Hashtbl.replace ext_eligible ext.pexp_loc names
          | None -> ())
      | _ -> ())
    !sites;
  { ext_eligible; record_eligible }

type comment_target =
  | Expression_target of Ppxlib.Parsetree.expression
  | Field_target of Ppxlib.Parsetree.label_declaration
  | Type_target of Ppxlib.Parsetree.core_type
  | Pattern_target of Ppxlib.Parsetree.pattern

type comment_assignment = {
  comment : source_comment;
  target : comment_target;
  (* True when the comment has more text after it on the same line, so it
     leads the target instead of trailing it. *)
  leads_target : bool;
  inline : bool;
  (* True for a return-type or let-binding type constraint: needs the
     plain marker, or the trailing-type rendering misprints before `=`. *)
  is_constraint_type : bool;
}

type documentation_placement = Record_field | Leading_only | Blank_after | Prefix

type documentation_comment = {
  placement : documentation_placement;
  is_documentation : bool;
  marker : string;
  text : string;
}

(* Reason attaches a /** ... */ comment as [@ocaml.doc] to whatever node
   follows, regardless of whether OCaml's grammar allows one there. *)
let documentation_attribute_text (attribute : Ppxlib.Parsetree.attribute) =
  match attribute with
  | {
      attr_name = { txt = "ocaml.doc" | "ocaml.text"; _ };
      attr_payload =
        PStr
          [
            {
              pstr_desc =
                Pstr_eval
                  ({ pexp_desc = Pexp_constant (Pconst_string (text, _, None)); _ }, _);
              _;
            };
          ];
      _;
    } ->
      Some text
  | _ -> None

let split_documentation attributes =
  List.fold_left
    (fun (kept, extracted) (attribute : Ppxlib.Parsetree.attribute) ->
      match documentation_attribute_text attribute with
      | Some text -> (kept, (text, attribute.attr_loc) :: extracted)
      | None -> (attribute :: kept, extracted))
    ([], []) attributes

(* Skip a `;`-terminated doc comment with nothing to document, or it
   prints twice. *)
let drop_documentation (attribute : attribute) documentation =
  List.filter
    (fun (candidate : attribute) ->
      not (String.equal candidate.attr_name.txt attribute.attr_name.txt))
    documentation

let documented_start old_start extracted =
  List.fold_left
    (fun start (_, (loc : Location.t)) ->
      if loc.loc_end.pos_cnum > start.Lexing.pos_cnum then loc.loc_end
      else start)
    old_start extracted

let after_leading_documentation ~text ~comments documentation (loc : Location.t) =
  let leading =
    List.filter_map
      (fun (attribute : attribute) ->
        if attribute.attr_loc.loc_start.pos_cnum = loc.loc_start.pos_cnum then
          Some ("", attribute.attr_loc)
        else None)
      documentation
  in
  let rec skip_comments (start : Lexing.position) =
    match comment_after_blanks ~text ~comments start.pos_cnum with
    | _, Some comment -> skip_comments comment.location.loc_end
    | _, None -> start
  in
  match leading with
  | [] -> loc
  | _ ->
      { loc with loc_start = skip_comments (documented_start loc.loc_start leading) }

let is_documentation_marker (item : structure_item) =
  match item.pstr_desc with
  | Pstr_attribute { attr_name = { txt; _ }; _ } ->
      String.starts_with ~prefix:"reason_to_mlx.doc_comment_" txt
  | _ -> false

(* `let%melange_only` prints its doc comment after the extension name,
   where OCaml attaches it to nothing. *)
let hoist_payload_documentation (item : structure_item) =
  match item.pstr_desc with
  | Pstr_extension (({ txt = "melange_only"; _ } as name, PStr payload), attributes) ->
      let hoisted = List.take_while is_documentation_marker payload in
      let payload = List.drop_while is_documentation_marker payload in
      ( hoisted,
        { item with pstr_desc = Pstr_extension ((name, PStr payload), attributes) } )
  | _ -> ([], item)

let blank_line_follows text offset =
  let rec go offset newlines =
    if newlines >= 2 then true
    else if offset >= String.length text then false
    else
      match text.[offset] with
      | '\n' -> go (offset + 1) (newlines + 1)
      | ' ' | '\t' | '\r' -> go (offset + 1) newlines
      | _ -> false
  in
  go offset 0

let preserve_documentation_comments ~text ~comments =
  object (self)
    inherit Ppxlib.Ast_traverse.map as super
    val mutable documentation_comments = []
    val mutable in_record_field = false
    val mutable in_exception = false
    val mutable in_expression = false
    val mutable next_marker = 0
    val mutable structure_item_documentation = []
    (* A doc comment on a bare expression or nested local `let` has no
       floating structure item to prepend before. *)
    val mutable expression_documentation = []
    (* Reason extends a documented node's location to cover its doc
       comment; a wrapping ancestor copies that same stale start. *)
    val mutable extended_starts = []
    method documentation_comments = List.rev documentation_comments
    method expression_documentation = List.rev expression_documentation

    method private rebase_loc_start (expression : Ppxlib.Parsetree.expression) =
      match
        List.assoc_opt expression.pexp_loc.loc_start.pos_cnum extended_starts
      with
      | Some loc_start ->
          { expression with pexp_loc = { expression.pexp_loc with loc_start } }
      | None -> expression

    method! expression expression =
      let previous_in_expression = in_expression in
      in_expression <- true;
      let result =
        match expression.pexp_desc with
        (* A let%extension payload must keep a leading doc comment as
           [@ocaml.doc]; ocamlformat-mlx prints it literally there. *)
        | Pexp_extension _ -> expression
        | _ -> (
            (* Strip before recursing, or method!attribute would see these
               first and keep them as genuine, item-style documentation. *)
            let kept, extracted = split_documentation expression.pexp_attributes in
            match extracted with
            | [] -> self#rebase_loc_start (super#expression expression)
            | extracted ->
                expression_documentation <- extracted @ expression_documentation;
                let old_start = expression.pexp_loc.loc_start in
                let loc_start = documented_start old_start extracted in
                extended_starts <- (old_start.pos_cnum, loc_start) :: extended_starts;
                self#rebase_loc_start
                  (super#expression
                     {
                       expression with
                       pexp_attributes = List.rev kept;
                       pexp_loc = { expression.pexp_loc with loc_start };
                     }))
      in
      in_expression <- previous_in_expression;
      result

    method! value_binding binding =
      if not in_expression then super#value_binding binding
      else
        let kept, extracted = split_documentation binding.pvb_attributes in
        match extracted with
        | [] -> super#value_binding binding
        | extracted ->
            expression_documentation <- extracted @ expression_documentation;
            (* Reason extends the binding's pvb_loc, not the tight
               pvb_pat.ppat_loc, to cover a leading doc comment. *)
            let old_start = binding.pvb_loc.loc_start in
            let loc_start = documented_start old_start extracted in
            extended_starts <- (old_start.pos_cnum, loc_start) :: extended_starts;
            super#value_binding
              { binding with pvb_attributes = List.rev kept; pvb_loc = { binding.pvb_loc with loc_start } }

    method! type_exception exception_ =
      let previous = in_exception in
      in_exception <- true;
      let exception_ = super#type_exception exception_ in
      in_exception <- previous;
      exception_

    method! label_declaration declaration =
      let previous = in_record_field in
      in_record_field <- true;
      let declaration = super#label_declaration declaration in
      in_record_field <- previous;
      declaration

    method private mark_blank_after documentation =
      match List.rev documentation with
      | (last : attribute) :: _ when blank_line_follows text last.attr_loc.loc_end.pos_cnum ->
          documentation_comments <-
            List.map
              (fun comment ->
                if String.equal comment.marker last.attr_name.txt && comment.placement = Prefix
                then { comment with placement = Blank_after }
                else comment)
              documentation_comments
      | _ -> ()

    method private collect_documentation : 'a. ('a -> 'a) -> 'a -> attribute list * 'a =
      fun f item ->
        let outer_documentation = structure_item_documentation in
        structure_item_documentation <- [];
        let item = f item in
        let documentation = List.rev structure_item_documentation in
        structure_item_documentation <- outer_documentation;
        (documentation, item)

    method! structure items =
      List.concat_map
        (fun item ->
          let documentation, item =
            self#collect_documentation
              (fun item ->
                (* A local module's structure is a fresh top-level-like
                   scope, even inside a function body. *)
                let outer_in_expression = in_expression in
                in_expression <- false;
                let item = super#structure_item item in
                in_expression <- outer_in_expression;
                item)
              item
          in
          (match item.pstr_desc with
          | Pstr_eval _ ->
              let markers =
                List.map
                  (fun (attribute : attribute) -> attribute.attr_name.txt)
                  documentation
              in
              documentation_comments <-
                List.map
                  (fun comment ->
                    if List.mem comment.marker markers then
                      { comment with is_documentation = false }
                    else comment)
                  documentation_comments
          | _ -> ());
          let documentation =
            match item.pstr_desc with
            | Pstr_attribute attribute ->
                drop_documentation attribute documentation
            | _ -> documentation
          in
          let item =
            { item with pstr_loc = after_leading_documentation ~text ~comments documentation item.pstr_loc }
          in
          self#mark_blank_after documentation;
          let hoisted, item = hoist_payload_documentation item in
          List.map Ppxlib.Ast_helper.Str.attribute documentation @ hoisted @ [ item ])
        items

    method! signature items =
      List.concat_map
        (fun item ->
          let documentation, item =
            self#collect_documentation super#signature_item item
          in
          let documentation =
            match item.psig_desc with
            | Psig_attribute attribute ->
                drop_documentation attribute documentation
            | _ -> documentation
          in
          let item =
            { item with psig_loc = after_leading_documentation ~text ~comments documentation item.psig_loc }
          in
          self#mark_blank_after documentation;
          List.map Ppxlib.Ast_helper.Sig.attribute documentation @ [ item ])
        items

    method! attribute (attribute : attribute) =
      match documentation_attribute_text attribute with
      | Some text ->
          let marker =
            Printf.sprintf "reason_to_mlx.doc_comment_%d" next_marker
          in
          next_marker <- next_marker + 1;
          documentation_comments <-
            {
              placement =
                (if in_record_field then Record_field
                 else if in_exception then Leading_only
                 else Prefix);
              is_documentation = true;
              marker;
              text;
            }
            :: documentation_comments;
          let attribute =
            {
              attribute with
              attr_name = { attribute.attr_name with txt = marker };
              attr_payload = PStr [];
            }
          in
          if not in_record_field then
            structure_item_documentation <-
              attribute :: structure_item_documentation;
          attribute
      | None -> super#attribute attribute
  end

(* The OCaml lexer reads string and character literals inside a comment; a
   string left open swallows the comment's closer. *)
let has_unterminated_string text =
  let length = String.length text in
  let rec code i =
    if i >= length then false
    else
      match text.[i] with
      | '"' -> string (i + 1)
      | '\'' when i + 2 < length && text.[i + 1] = '"' && text.[i + 2] = '\'' -> code (i + 3)
      | _ -> code (i + 1)
  and string i =
    if i >= length then true
    else
      match text.[i] with
      | '\\' -> string (i + 2)
      | '"' -> code (i + 1)
      | _ -> string (i + 1)
  in
  code 0

let escape_ocaml_comment text =
  let needs_quote_escaping = has_unterminated_string text in
  let length = String.length text in
  let nested_comments_balanced =
    let rec scan i depth =
      if i + 1 >= length then depth = 0
      else
        match (text.[i], text.[i + 1]) with
        | '(', '*' -> scan (i + 2) (depth + 1)
        | '*', ')' -> depth > 0 && scan (i + 2) (depth - 1)
        | _ -> scan (i + 1) depth
    in
    scan 0 0
  in
  (* The comment lexer treats `{delim|...|delim}` as a quoted string; only
     an opener with no closer needs an escaping space. *)
  let is_lower c = (c >= 'a' && c <= 'z') || c = '_' in
  let is_ext_char c =
    is_lower c || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c = '\'' || c = '.'
  in
  let skip_while pred i =
    let i = ref i in
    while !i < length && pred text.[!i] do incr i done;
    !i
  in
  let classify_brace offset =
    let after_prefix =
      let i = offset + 1 in
      if i < length && text.[i] = '%' then
        let i = if i + 1 < length && text.[i + 1] = '%' then i + 2 else i + 1 in
        let ident_end = skip_while is_ext_char i in
        if ident_end > i then skip_while (fun c -> c = ' ' || c = '\t') ident_end
        else offset + 1
      else i
    in
    let delim_end = skip_while is_lower after_prefix in
    if delim_end >= length || text.[delim_end] <> '|' then `Plain
    else
      let closer = "|" ^ String.sub text after_prefix (delim_end - after_prefix) ^ "}" in
      let closer_length = String.length closer in
      let rec find i =
        if i + closer_length > length then `Unclosed
        else if String.sub text i closer_length = closer then `Closed (i + closer_length)
        else find (i + 1)
      in
      find (delim_end + 1)
  in
  let buffer = Buffer.create length in
  let rec loop previous offset quoted_until =
    if offset < length then (
      let char = text.[offset] in
      let () =
        match (previous, char) with
        | (Some '(', '*' | Some '*', ')') when not nested_comments_balanced ->
            Buffer.add_char buffer ' '
        | _ -> ()
      in
      Buffer.add_char buffer char;
      if char = '"' && needs_quote_escaping then Buffer.add_char buffer '"';
      let quoted_until =
        if char = '{' && offset >= quoted_until then
          match classify_brace offset with
          | `Plain -> quoted_until
          | `Closed end_offset -> end_offset
          | `Unclosed ->
              Buffer.add_char buffer ' ';
              quoted_until
        else quoted_until
      in
      loop (Some char) (offset + 1) quoted_until)
  in
  loop None 0 0;
  Buffer.contents buffer

let is_line_comment_at source offset =
  offset + 1 < String.length source && source.[offset] = '/' && source.[offset + 1] = '/'

let source_comment source id (text, location) =
  let start_offset = location.Location.loc_start.Lexing.pos_cnum in
  let is_line_comment = is_line_comment_at source start_offset in
  let chop suffix text =
    if String.ends_with ~suffix text then
      String.sub text 0 (String.length text - String.length suffix)
    else text
  in
  let text = if is_line_comment then chop "\r" (chop "\n" text) ^ " " else text in
  let location =
    if is_line_comment then
      let stop =
        match String.index_from_opt source start_offset '\n' with
        | Some newline -> newline + 1
        | None -> String.length source
      in
      { location with loc_end = { location.loc_end with pos_cnum = stop } }
    else location
  in
  { id; text; location }

let starts_own_line text (comment : source_comment) =
  let rec blank_back i =
    i < 0 || (match text.[i] with '\n' -> true | ' ' | '\t' | '\r' -> blank_back (i - 1) | _ -> false)
  in
  blank_back (comment.location.loc_start.pos_cnum - 1)

let merge_split_quote_comments source comments =
  let column (comment : source_comment) =
    comment.location.loc_start.pos_cnum - comment.location.loc_start.pos_bol
  in
  let own_line_comment comment =
    is_line_comment_at source comment.location.loc_start.pos_cnum
    && starts_own_line source comment
  in
  let continues (previous : source_comment) (comment : source_comment) =
    own_line_comment previous && own_line_comment comment
    && comment.location.loc_start.pos_lnum = previous.location.loc_end.pos_lnum + 1
    && column comment = column previous
  in
  let without_trailing_blanks =
    String.drop_last_while (fun char -> char = ' ' || char = '\t')
  in
  let join (run : source_comment) (comment : source_comment) =
    let indent = String.make (column comment + 2) ' ' in
    let line = without_trailing_blanks comment.text in
    let line = if String.equal line "" then "" else indent ^ line in
    {
      run with
      text = without_trailing_blanks run.text ^ "\n" ^ line ^ " ";
      location = { run.location with loc_end = comment.location.loc_end };
    }
  in
  let unterminated (comment : source_comment) = has_unterminated_string comment.text in
  let merge = function
    | first :: rest as run when List.exists unterminated run ->
        let merged = List.fold_left join first rest in
        if unterminated merged then run else [ merged ]
    | run -> run
  in
  List.sort
    (fun (a : source_comment) (b : source_comment) ->
      compare a.location.loc_start.pos_cnum b.location.loc_start.pos_cnum)
    comments
  |> List.fold_left
       (fun runs comment ->
         match runs with
         | (previous :: _ as run) :: runs when continues previous comment ->
             (comment :: run) :: runs
         | runs -> [ comment ] :: runs)
       []
  |> List.rev_map (fun run -> merge (List.rev run))
  |> List.concat
  |> List.mapi (fun id (comment : source_comment) -> { comment with id })

let print_comment_text text =
  let text = escape_ocaml_comment text in
  let prefix =
    if String.length text > 0 && (text.[0] = '*' || text.[0] = ')') then " "
    else ""
  in
  let suffix =
    if String.length text > 0 && text.[String.length text - 1] = '(' then " "
    else ""
  in
  "(*" ^ prefix ^ text ^ suffix ^ "*)"

let marker_name kind comment =
  "reason_to_mlx." ^ kind ^ "_" ^ string_of_int comment.id

let marker_attribute kind comment =
  Ppxlib.Ast_helper.Attr.mk ~loc:comment.location
    { txt = marker_name kind comment; loc = comment.location }
    (PStr [])

let with_expr_markers kind leads (e : Ppxlib.Parsetree.expression) =
  {
    e with
    pexp_attributes = e.pexp_attributes @ List.map (marker_attribute kind) leads;
  }

let with_pat_markers kind leads (p : Ppxlib.Parsetree.pattern) =
  {
    p with
    ppat_attributes = p.ppat_attributes @ List.map (marker_attribute kind) leads;
  }

let with_case_markers kind leads (c : Ppxlib.Parsetree.case) =
  { c with pc_lhs = with_pat_markers kind leads c.pc_lhs }

let with_binding_markers kind leads (b : Ppxlib.Parsetree.value_binding) =
  { b with pvb_pat = with_pat_markers kind leads b.pvb_pat }

let with_field_markers kind leads (f : Ppxlib.Parsetree.label_declaration) =
  {
    f with
    pld_attributes = f.pld_attributes @ List.map (marker_attribute kind) leads;
  }

let with_row_field_markers kind leads (f : Ppxlib.Parsetree.row_field) =
  {
    f with
    prf_attributes = f.prf_attributes @ List.map (marker_attribute kind) leads;
  }

let with_constructor_markers kind leads
    (c : Ppxlib.Parsetree.constructor_declaration) =
  {
    c with
    pcd_attributes = c.pcd_attributes @ List.map (marker_attribute kind) leads;
  }

let expr_cnum (e : Ppxlib.Parsetree.expression) = e.pexp_loc.loc_start.pos_cnum

let with_cons (expression : Ppxlib.Parsetree.expression) cons pair head tail =
  {
    expression with
    pexp_desc =
      Pexp_construct
        ( cons,
          Some { pair with pexp_desc = Pexp_tuple [ head; tail ] } );
  }

let map_param_pattern f (param : Ppxlib.Parsetree.function_param) =
  match param.pparam_desc with
  | Pparam_val (label, default, pattern) ->
      { param with pparam_desc = Pparam_val (label, default, f pattern) }
  | Pparam_newtype _ -> param

let map_first_binding f (e : Ppxlib.Parsetree.expression) =
  match e.pexp_desc with
  | Pexp_let (recflag, first :: rest, body) ->
      { e with pexp_desc = Pexp_let (recflag, f first :: rest, body) }
  | _ -> e

let is_jsx_attribute (attribute : Ppxlib.Parsetree.attribute) =
  String.equal attribute.attr_name.txt "JSX"

let is_react_component_attribute_name = function
  | "react.component" | "react.client.component" | "react.async.component" ->
      true
  | _ -> false

(* A locally abstract type's name must stay unparenthesized to parse. *)
let has_locally_abstract_constraint (binding : Ppxlib.Parsetree.value_binding)
    =
  match binding.pvb_constraint with
  | Some (Pvc_constraint { locally_abstract_univars = _ :: _; _ })
    ->
      true
  | _ -> false

(* Reason parses a return type as a body constraint that starts before the body. *)
let rec reason_return_type_constraint
    (constraint_ : Ppxlib.Parsetree.type_constraint option)
    (body : Ppxlib.Parsetree.function_body) :
    Ppxlib.Parsetree.type_constraint option * Ppxlib.Parsetree.function_body =
  match (constraint_, body) with
  | None, Pfunction_body expr -> (
      match expr.pexp_desc with
      | Pexp_function (inner_params, inner_constraint, inner_body)
        when expr.pexp_attributes = [] ->
          let inner_constraint, inner_body =
            reason_return_type_constraint inner_constraint inner_body
          in
          ( None,
            Pfunction_body
              {
                expr with
                pexp_desc =
                  Pexp_function (inner_params, inner_constraint, inner_body);
              } )
      | Pexp_constraint (e, t)
        when expr.pexp_attributes = []
             && t.ptyp_loc.loc_start.pos_cnum < e.pexp_loc.loc_start.pos_cnum
        ->
          (Some (Pconstraint t), Pfunction_body e)
      | _ -> (constraint_, body))
  | _ -> (constraint_, body)

let is_infix_operator_name name =
  String.length name > 0
  && String.contains "!$%&*+-./:<=>?@^|~" name.[0]

let preserve_leading_comments ~text ast (comments : source_comment list) =
  let remaining = ref comments in
  let comment_covers = offset_in_comment comments in
  let precedes_label (c : source_comment) ~value_cnum =
    let rec scan offset =
      offset < value_cnum
      && (((text.[offset] = '~' || text.[offset] = '?')
          && not (comment_covers offset))
         || scan (offset + 1))
    in
    scan c.location.loc_end.pos_cnum
  in
  let take_from ~any_line ~max_end_lnum ~(after : Location.t) ~before_cnum =
    let selected, rest =
      List.partition
        (fun (c : source_comment) ->
          after.Location.loc_end.pos_cnum <= c.location.loc_start.pos_cnum
          && c.location.loc_end.pos_lnum <= max_end_lnum
          && c.location.loc_end.pos_cnum <= before_cnum
          && (any_line || c.location.loc_start.pos_lnum > after.loc_end.pos_lnum))
        !remaining
    in
    remaining := rest;
    selected
  in
  let take_gap = take_from ~any_line:false ~max_end_lnum:max_int in
  let take_gap_any_line = take_from ~any_line:true ~max_end_lnum:max_int in
  let take_gap_above_line ~(after : Location.t) ~(before : Location.t) =
    take_from ~any_line:false
      ~max_end_lnum:(before.loc_start.pos_lnum - 1)
      ~after ~before_cnum:before.loc_start.pos_cnum
  in
  let take_gap_before_line ~(after : Location.t) ~(before : Location.t) =
    take_from ~any_line:true
      ~max_end_lnum:(before.loc_start.pos_lnum - 1)
      ~after ~before_cnum:before.loc_start.pos_cnum
  in
  let only_blank_or_comments ~start ~stop =
    let rec go offset =
      offset >= stop
      || (Char.Ascii.is_white text.[offset] || comment_covers offset)
         && go (offset + 1)
    in
    go start
  in
  let take_gap_before_first_field ~(after : Location.t) ~(before : Location.t) =
    let before_cnum = before.loc_start.pos_cnum in
    let on_header_line = take_gap_before_line ~after ~before in
    let below_header = take_gap ~after ~before_cnum in
    let selected, rest =
      List.partition
        (fun (c : source_comment) ->
          after.loc_end.pos_cnum <= c.location.loc_start.pos_cnum
          && c.location.loc_end.pos_cnum <= before_cnum
          && only_blank_or_comments ~start:c.location.loc_end.pos_cnum
               ~stop:before_cnum)
        !remaining
    in
    remaining := rest;
    on_header_line @ below_header @ selected
  in
  let is_jsx_attributed (expression : Ppxlib.Parsetree.expression) =
    List.exists is_jsx_attribute expression.pexp_attributes
  in
  (* A pipe call (`a->f(b)`) desugars to `Pexp_apply (f, [a; b])` with `f`
     keeping a later position, so the leftmost child isn't always `f`. *)
  let rec leftmost_location (e : Ppxlib.Parsetree.expression) =
    match e.Ppxlib.Parsetree.pexp_desc with
    | Pexp_apply (callee, arguments) ->
        let leftmost =
          List.fold_left
            (fun (best : Ppxlib.Parsetree.expression) (_, (argument : Ppxlib.Parsetree.expression)) ->
              if argument.pexp_loc.loc_start.pos_cnum < best.pexp_loc.loc_start.pos_cnum
              then argument
              else best)
            callee arguments
        in
        leftmost_location leftmost
    | Pexp_sequence (first, _) -> leftmost_location first
    | Pexp_tuple (first :: _) -> leftmost_location first
    | Pexp_field (record, _) -> leftmost_location record
    | Pexp_setfield (record, _, _) -> leftmost_location record
    | Pexp_send (obj, _) -> leftmost_location obj
    | Pexp_match (subject, _) -> leftmost_location subject
    | Pexp_ident identifier -> identifier.loc
    | _ -> e.pexp_loc
  in
  let rec lead_body_location (body : Ppxlib.Parsetree.expression) =
    match body.Ppxlib.Parsetree.pexp_desc with
    | Pexp_function (_, _, Pfunction_body inner) ->
        lead_body_location inner
    | Pexp_let (_, first_binding :: _, _)
      when not (has_locally_abstract_constraint first_binding) ->
        first_binding.Ppxlib.Parsetree.pvb_pat.ppat_loc
    (* A `module M = ...;` statement is transparent: the comment still
       leads whatever comes after it. *)
    | Pexp_letmodule (_, _, inner) -> lead_body_location inner
    (* A bare `fun | pattern => ...` leads its first case the same way a
       `switch` leads its first arm. *)
    | Pexp_function
        (_, _, Pfunction_cases (first_case :: _, _, _)) ->
        first_case.Ppxlib.Parsetree.pc_lhs.ppat_loc
    | _ -> leftmost_location body
  in
  let rec attach_lead_body leads (body : Ppxlib.Parsetree.expression) =
    match body.Ppxlib.Parsetree.pexp_desc with
    | Pexp_function (params, constraint_, Pfunction_body inner)
      ->
        {
          body with
          pexp_desc =
            Pexp_function
              (params, constraint_, Pfunction_body (attach_lead_body leads inner));
        }
    | Pexp_let (_, first_binding :: _, _)
      when not (has_locally_abstract_constraint first_binding) ->
        map_first_binding (with_binding_markers "lead" leads) body
    | Pexp_letmodule (name, mexpr, inner) ->
        let before, after =
          List.partition
            (fun (c : source_comment) ->
              c.location.loc_end.pos_cnum <= name.loc.loc_start.pos_cnum)
            leads
        in
        with_expr_markers "leadin" before
          {
            body with
            pexp_desc = Pexp_letmodule (name, mexpr, attach_lead_body after inner);
          }
    | Pexp_function
        (params, constraint_, Pfunction_cases (first_case :: rest, cases_loc, cases_attrs))
      ->
        let first_case = with_case_markers "lead" leads first_case in
        {
          body with
          pexp_desc =
            Pexp_function
              ( params,
                constraint_,
                Pfunction_cases (first_case :: rest, cases_loc, cases_attrs) );
        }
    | _ ->
        with_expr_markers "leadin" leads body
  in
  let is_leaf_lambda_body (body : Ppxlib.Parsetree.expression) =
    (not (is_jsx_attributed body))
    &&
    match body.pexp_desc with
    | Pexp_let _ | Pexp_function _ | Pexp_letmodule _ -> false
    | _ -> true
  in
  let lead_block_body ~after (body : Ppxlib.Parsetree.expression) =
    let before_cnum = (lead_body_location body).Location.loc_start.pos_cnum in
    attach_lead_body (take_gap ~after ~before_cnum) body
  in
  let lead_each ~after ~start ~finish ~mark items =
    let rec go previous = function
      | [] -> []
      | item :: rest ->
          let item = mark (take_gap ~after:previous ~before_cnum:(start item)) item in
          item :: go (finish item) rest
    in
    go after items
  in
  let lead_record_fields ~after fields =
    match fields with
    | [] -> []
    | (first : Ppxlib.Parsetree.label_declaration) :: rest ->
        let first =
          with_field_markers "leadfield"
            (take_gap_before_first_field ~after ~before:first.pld_loc)
            first
        in
        first
        :: lead_each ~after:first.pld_loc
             ~start:(fun (f : Ppxlib.Parsetree.label_declaration) ->
               f.pld_loc.loc_start.pos_cnum)
             ~finish:(fun (f : Ppxlib.Parsetree.label_declaration) -> f.pld_loc)
             ~mark:(with_field_markers "leadlist") rest
  in
  let lead_bindings bindings =
    match bindings with
    | [] -> []
    | (first : Ppxlib.Parsetree.value_binding) :: rest ->
        first
        :: lead_each ~after:first.pvb_expr.pexp_loc
             ~start:(fun (b : Ppxlib.Parsetree.value_binding) ->
               b.pvb_pat.ppat_loc.loc_start.pos_cnum)
             ~finish:(fun (b : Ppxlib.Parsetree.value_binding) -> b.pvb_expr.pexp_loc)
             ~mark:(fun leads b ->
               if has_locally_abstract_constraint b then (
                 remaining := leads @ !remaining;
                 b)
               else with_binding_markers "lead" leads b)
             rest
  in
  let mapper =
    object (self)
      inherit Ppxlib.Ast_traverse.map as super

      method walk_jsx_children ?previous (value : Ppxlib.Parsetree.expression) =
        match value.pexp_desc with
        | Pexp_construct
            ( ({ txt = Lident "::"; _ } as cons),
              Some ({ pexp_desc = Pexp_tuple [ head; tail ]; _ } as pair) ) ->
            let head = self#expression head in
            let head =
              match previous with
              | Some (previous : Ppxlib.Parsetree.expression)
                when not (is_jsx_attributed previous) ->
                  with_expr_markers "leadlist"
                    (take_gap ~after:previous.pexp_loc
                       ~before_cnum:(expr_cnum head))
                    head
              | Some _ | None -> head
            in
            with_cons value cons pair head
              (self#walk_jsx_children ~previous:head tail)
        | _ -> self#expression value

      method! expression expression =
        let expression =
          match expression.Ppxlib.Parsetree.pexp_desc with
          | Pexp_apply (callee, arguments)
            when is_jsx_attributed expression ->
              let callee = self#expression callee in
              let arguments =
                List.map
                  (fun (label, (value : Ppxlib.Parsetree.expression)) ->
                    match label with
                    | Labelled "children" ->
                        (label, self#walk_jsx_children value)
                    | _ -> (label, self#expression value))
                  arguments
              in
              { expression with pexp_desc = Pexp_apply (callee, arguments) }
          | Pexp_construct
              ( ({ txt = Lident "::"; _ }, Some _) )
            when is_jsx_attributed expression ->
              (* A fragment's children are JSX directly on the cons chain,
                 not wrapped in an apply. *)
              self#walk_jsx_children expression
          | Pexp_construct
              ( ({ txt = Lident "::"; _ } as cons),
                Some ({ pexp_desc = Pexp_tuple [ head; tail ]; _ } as pair) )
            ->
              let head = self#expression head in
              with_cons expression cons pair head (self#expression tail)
          | _ -> super#expression expression
        in
        let expression =
          match expression.Ppxlib.Parsetree.pexp_desc with
          | Pexp_apply
              ( ({ pexp_desc = Pexp_ident { txt = Lident operator_name; _ }; _ } as
                 operator),
                [ (Nolabel, lhs); (Nolabel, rhs) ] )
            when is_infix_operator_name operator_name
                 && (not (String.equal operator_name "|."))
                 && not (is_jsx_attributed expression) ->
              let leads =
                take_gap ~after:lhs.pexp_loc
                  ~before_cnum:operator.pexp_loc.loc_start.pos_cnum
              in
              {
                expression with
                pexp_desc =
                  Pexp_apply
                    ( operator,
                      [ (Nolabel, lhs); (Nolabel, with_expr_markers "leadoperator" leads rhs) ]
                    );
              }
          | _ -> expression
        in
        match expression.Ppxlib.Parsetree.pexp_desc with
        | Pexp_let (recflag, bindings, body) -> (
            let bindings = lead_bindings bindings in
            match List.rev bindings with
            | [] -> expression
            | last_binding :: _ -> (
                let leads =
                  take_gap ~after:last_binding.pvb_expr.pexp_loc
                    ~before_cnum:(expr_cnum body)
                in
                let with_body body =
                  { expression with pexp_desc = Pexp_let (recflag, bindings, body) }
                in
                match body.pexp_desc with
                | Pexp_let (_, next_binding :: _, _)
                  when not (has_locally_abstract_constraint next_binding) ->
                    with_body
                      (map_first_binding (with_binding_markers "lead" leads) body)
                | _ -> with_body (with_expr_markers "leadin" leads body)))
        | Pexp_match (subject, cases) ->
            let attach_body_lead (case : Ppxlib.Parsetree.case) =
              (* A JSX case body drops a comment even with a blank line. *)
              if is_jsx_attributed case.pc_rhs then case
              else
                let after =
                  match case.pc_guard with
                  | Some guard -> guard.pexp_loc
                  | None -> case.pc_lhs.ppat_loc
                in
                let leads =
                  take_gap ~after
                    ~before_cnum:case.pc_rhs.pexp_loc.loc_start.pos_cnum
                in
                {
                  case with
                  pc_rhs = with_expr_markers "leadcasebody" leads case.pc_rhs;
                }
            in
            let attach_guard_lead (case : Ppxlib.Parsetree.case) =
              match case.pc_guard with
              | None -> case
              | Some guard ->
                  let leads =
                    take_gap ~after:case.pc_lhs.ppat_loc
                      ~before_cnum:(expr_cnum guard)
                  in
                  { case with pc_guard = Some (with_expr_markers "leadguard" leads guard) }
            in
            let cases = List.map (fun case -> attach_body_lead (attach_guard_lead case)) cases in
            let cases =
              lead_each ~after:subject.pexp_loc
                ~start:(fun (c : Ppxlib.Parsetree.case) ->
                  c.pc_lhs.ppat_loc.loc_start.pos_cnum)
                ~finish:(fun (c : Ppxlib.Parsetree.case) -> c.pc_rhs.pexp_loc)
                ~mark:(with_case_markers "lead") cases
            in
            { expression with pexp_desc = Pexp_match (subject, cases) }
        | Pexp_apply
            ( ({ pexp_desc = Pexp_ident { txt = Lident "|."; _ }; _ } as
               operator),
              [ (Nolabel, lhs); (Nolabel, rhs) ] ) ->
            let leads =
              take_gap ~after:lhs.pexp_loc
                ~before_cnum:(leftmost_location rhs).loc_start.pos_cnum
            in
            let rhs = with_expr_markers "leadoperator" leads rhs in
            {
              expression with
              pexp_desc =
                Pexp_apply (operator, [ (Nolabel, lhs); (Nolabel, rhs) ]);
            }
        | Pexp_apply (callee, arguments)
          when not (is_jsx_attributed expression) ->
            (* ocamlformat-mlx drops a JSX argument's label if trailed. *)
            let rec attach_to_body leads (target : Ppxlib.Parsetree.expression)
                =
              match target.pexp_desc with
              | Pexp_function
                  (params, constraint_, Pfunction_body body) -> (
                  let body =
                    match attach_to_body leads body with
                    | Some body -> Some body
                    | None when is_leaf_lambda_body body ->
                        Some (with_expr_markers "leadcasebody" leads body)
                    | None -> None
                  in
                  match body with
                  | None -> None
                  | Some body ->
                      Some
                        {
                          target with
                          pexp_desc =
                            Pexp_function (params, constraint_, Pfunction_body body);
                        })
              | Pexp_let (_, first_binding :: _, _)
                when not (has_locally_abstract_constraint first_binding) ->
                  Some
                    (map_first_binding
                       (with_binding_markers "lead" leads)
                       target)
              | _ -> None
            in
            let rec target_location (value : Ppxlib.Parsetree.expression) =
              match value.pexp_desc with
              | Pexp_function (_, _, Pfunction_body body) -> (
                  match target_location body with
                  | Some location -> Some location
                  | None when is_leaf_lambda_body body ->
                      Some (lead_body_location body)
                  | None -> None)
              | Pexp_let (_, first_binding :: _, _)
                when not (has_locally_abstract_constraint first_binding) ->
                  Some first_binding.Ppxlib.Parsetree.pvb_pat.ppat_loc
              | _ -> None
            in
            let split_label_leads label value leads =
              match label with
              | Labelled _ | Optional _ ->
                  List.partition
                    (precedes_label ~value_cnum:(expr_cnum value))
                    leads
              | Nolabel -> ([], leads)
            in
            let rec walk = function
              | [] -> []
              | (label, (arg : Ppxlib.Parsetree.expression)) :: rest -> (
                  match rest with
                  | (next_label, next_arg) :: rest_tail -> (
                      match target_location next_arg with
                      | Some target_loc -> (
                          let leads =
                            take_gap ~after:arg.pexp_loc
                              ~before_cnum:target_loc.loc_start.pos_cnum
                          in
                          let own_line, leads =
                            split_label_leads next_label next_arg leads
                          in
                          let own_line_arg next_arg =
                            with_expr_markers "leadargown" own_line next_arg
                          in
                          match attach_to_body leads next_arg with
                          | Some next_arg ->
                              (label, arg)
                              :: walk
                                   ((next_label, own_line_arg next_arg)
                                   :: rest_tail)
                          | None ->
                              (label, with_expr_markers "leadarg" leads arg)
                              :: walk
                                   ((next_label, own_line_arg next_arg)
                                   :: rest_tail))
                      | None ->
                          let next_arg =
                            match next_label with
                            | Labelled _ | Optional _ ->
                                let leads =
                                  take_gap ~after:arg.pexp_loc
                                    ~before_cnum:(expr_cnum next_arg)
                                in
                                let leads, after_label =
                                  split_label_leads next_label next_arg leads
                                in
                                remaining := after_label @ !remaining;
                                with_expr_markers "leadargown" leads next_arg
                            | Nolabel -> next_arg
                          in
                          (label, arg) :: walk ((next_label, next_arg) :: rest_tail))
                  | [] -> [ (label, arg) ])
            in
            let arguments =
              match arguments with
              | (label, first) :: rest -> (
                  match target_location first with
                  | Some target_loc -> (
                      let leads =
                        take_gap ~after:callee.pexp_loc
                          ~before_cnum:target_loc.loc_start.pos_cnum
                      in
                      let own_line, inner = split_label_leads label first leads in
                      match attach_to_body inner first with
                      | Some first ->
                          (label, with_expr_markers "leadargown" own_line first)
                          :: rest
                      | None ->
                          remaining := leads @ !remaining;
                          arguments)
                  | None -> (
                      match label with
                      | Labelled _ | Optional _ ->
                          ( label,
                            with_expr_markers "leadargown"
                              (take_gap ~after:callee.pexp_loc
                                 ~before_cnum:(expr_cnum first))
                              first )
                          :: rest
                      | Nolabel -> arguments))
              | [] -> arguments
            in
            let arguments = walk arguments in
            { expression with pexp_desc = Pexp_apply (callee, arguments) }
        (* A gap before or between JSX props otherwise lands on the tag or
           inside the earlier prop's own parens (a call, a negative literal). *)
        | Pexp_apply (callee, arguments)
          when is_jsx_attributed expression ->
            (* [after] is the callee or the previous prop. Before the first prop
               a comment on the value's own line may sit between label and
               value, which the AST cannot tell apart from a lead. *)
            let rec walk ~(after : Location.t) ~after_is_callee ~after_is_jsx =
              function
              | [] -> []
              | (Nolabel, _ as unit_argument) :: rest ->
                  unit_argument :: walk ~after ~after_is_callee ~after_is_jsx rest
              | ( (Labelled "children" as label),
                  ({
                     pexp_desc =
                       Pexp_construct
                         ( cons,
                           Some ({ pexp_desc = Pexp_tuple [ head; tail ]; _ } as pair)
                         );
                     _;
                   } as children) )
                :: rest ->
                  let own_line = take_gap ~after ~before_cnum:(expr_cnum head) in
                  let tag_line =
                    if is_jsx_attributed head then
                      take_gap_any_line ~after ~before_cnum:(expr_cnum head)
                    else take_gap_before_line ~after ~before:head.pexp_loc
                  in
                  let head = with_expr_markers "leadlist" (own_line @ tag_line) head in
                  (label, with_cons children cons pair head tail) :: rest
              | ((Labelled "children", _) as children) :: rest ->
                  children :: rest
              | (label, (arg : Ppxlib.Parsetree.expression)) :: rest ->
                  let before_cnum = arg.pexp_loc.loc_start.pos_cnum in
                  let arg =
                    if after_is_callee then
                      with_expr_markers "leadargown"
                        (take_gap_above_line ~after ~before:arg.pexp_loc)
                        arg
                    else if after_is_jsx then
                      (* The printer puts a comment after a JSX-valued prop
                         inside that prop's parens, so only a comment on a
                         later line leads the next prop, ahead of its value. *)
                      with_expr_markers "leadvalue"
                        (take_gap ~after ~before_cnum)
                        arg
                    else
                      (* A same-line comment stays on the prop it
                         followed, not past a lambda-valued next prop. *)
                      let leads = take_gap_any_line ~after ~before_cnum in
                      let own_line, same_line =
                        List.partition
                          (fun (c : source_comment) ->
                            c.location.loc_start.pos_lnum > after.loc_end.pos_lnum)
                          leads
                      in
                      arg
                      |> with_expr_markers "leadarg" same_line
                      |> with_expr_markers "leadargown" own_line
                  in
                  (label, arg)
                  :: walk ~after:arg.pexp_loc ~after_is_callee:false
                       ~after_is_jsx:(is_jsx_attributed arg) rest
            in
            {
              expression with
              pexp_desc =
                Pexp_apply
                  (callee,
                   walk ~after:callee.pexp_loc ~after_is_callee:true
                     ~after_is_jsx:false arguments);
            }
        (* A fragment's children are a cons chain too, so its first child
           leads the same way a list element does. *)
        | Pexp_construct
            ( ({ txt = Lident "::"; _ } as cons),
              Some ({ pexp_desc = Pexp_tuple [ head; tail ]; _ } as pair) ) -> (
            (* The outer cons cell's location starts at the list's own
               opening bracket, before the first element. *)
            let anchor =
              { expression.pexp_loc with loc_end = expression.pexp_loc.loc_start }
            in
            let before_head_leads =
              take_gap_before_line ~after:anchor ~before:head.pexp_loc
            in
            let head = with_expr_markers "leadlist" before_head_leads head in
            let tail =
              match tail.pexp_desc with
              | Pexp_construct
                  ( tail_cons,
                    Some
                      ({ pexp_desc = Pexp_tuple (next_head :: tail_rest); _ } as
                       tail_pair) ) ->
                  let next_head =
                    with_expr_markers "leadlist"
                      (take_gap ~after:head.pexp_loc
                         ~before_cnum:(expr_cnum next_head))
                      next_head
                  in
                  {
                    tail with
                    pexp_desc =
                      Pexp_construct
                        ( tail_cons,
                          Some
                            {
                              tail_pair with
                              pexp_desc = Pexp_tuple (next_head :: tail_rest);
                            } );
                  }
              | _ -> tail
            in
            with_cons expression cons pair head tail)
        (* A cons chain's trailing [] is a ghost node reusing the tail's
           span, not a real empty list, so ghost locations are excluded. *)
        | Pexp_construct
            ({ txt = Lident "[]"; _ }, None)
          when (not (is_jsx_attributed expression))
               && not expression.pexp_loc.loc_ghost -> (
            let anchor =
              { expression.pexp_loc with loc_end = expression.pexp_loc.loc_start }
            in
            let leads =
              take_gap_any_line ~after:anchor
                ~before_cnum:expression.pexp_loc.loc_end.pos_cnum
            in
            with_expr_markers "leadlistempty" leads expression)
        | Pexp_tuple (first :: rest) ->
            let rest =
              lead_each ~after:first.pexp_loc ~start:expr_cnum
                ~finish:(fun (e : Ppxlib.Parsetree.expression) -> e.pexp_loc)
                ~mark:(with_expr_markers "leadlist") rest
            in
            { expression with pexp_desc = Pexp_tuple (first :: rest) }
        | Pexp_record ((first_label, first_value) :: rest, base) ->
            let leads =
              match base with
              | Some base ->
                  take_gap_any_line ~after:base.pexp_loc
                    ~before_cnum:(expr_cnum first_value)
              | None ->
                  let anchor =
                    { expression.pexp_loc with loc_end = expression.pexp_loc.loc_start }
                  in
                  take_gap_before_line ~after:anchor ~before:first_label.loc
            in
            let first =
              (first_label, with_expr_markers "leadrecordfield" leads first_value)
            in
            let rest =
              lead_each ~after:first_value.pexp_loc
                ~start:(fun (_, v) -> expr_cnum v)
                ~finish:(fun (_, (v : Ppxlib.Parsetree.expression)) -> v.pexp_loc)
                ~mark:(fun leads (label, v) ->
                  (label, with_expr_markers "leadrecordfield" leads v))
                rest
            in
            { expression with pexp_desc = Pexp_record (first :: rest, base) }
        | Pexp_open (declaration, body) ->
            let leads =
              take_gap_any_line ~after:declaration.popen_loc
                ~before_cnum:(lead_body_location body).Location.loc_start.pos_cnum
            in
            {
              expression with
              pexp_desc = Pexp_open (declaration, attach_lead_body leads body);
            }
        | Pexp_ifthenelse (cond, then_, else_) ->
            let then_ = lead_block_body ~after:cond.pexp_loc then_ in
            let else_ =
              match else_ with
              | None -> None
              | Some else_ -> Some (lead_block_body ~after:then_.pexp_loc else_)
            in
            { expression with pexp_desc = Pexp_ifthenelse (cond, then_, else_) }
        | Pexp_while (cond, body) ->
            {
              expression with
              pexp_desc = Pexp_while (cond, lead_block_body ~after:cond.pexp_loc body);
            }
        | Pexp_for (pattern, start, stop, direction, body) ->
            {
              expression with
              pexp_desc =
                Pexp_for
                  (pattern, start, stop, direction,
                   lead_block_body ~after:stop.pexp_loc body);
            }
        | Pexp_sequence (first, second) ->
            {
              expression with
              pexp_desc =
                Pexp_sequence (first, lead_block_body ~after:first.pexp_loc second);
            }
        | _ -> expression

      method! structure_item item =
        let item = super#structure_item item in
        match item.pstr_desc with
        | Pstr_value (recflag, bindings) ->
            { item with pstr_desc = Pstr_value (recflag, lead_bindings bindings) }
        | _ -> item

      method! pattern pattern =
        let pattern = super#pattern pattern in
        match pattern.ppat_desc with
        | Ppat_record (((_, (first : Ppxlib.Parsetree.pattern)) as first_field) :: rest, closed) ->
            let rest =
              lead_each ~after:first.ppat_loc
                ~start:(fun ((label : Ppxlib.Longident.t Location.loc), _) ->
                  label.loc.loc_start.pos_cnum)
                ~finish:(fun (_, (p : Ppxlib.Parsetree.pattern)) -> p.ppat_loc)
                ~mark:(fun leads (label, p) ->
                  (label, with_pat_markers "leadpatternfield" leads p))
                rest
            in
            { pattern with ppat_desc = Ppat_record (first_field :: rest, closed) }
        | _ -> pattern

      method! value_binding binding =
        let binding = super#value_binding binding in
        (* Without this, a comment after [@react.component] falls back to
           the whole body and prints after the function, not the attribute. *)
        let binding =
          match
            List.find_opt
              (fun (attribute : Ppxlib.Parsetree.attribute) ->
                is_react_component_attribute_name attribute.attr_name.txt)
              binding.pvb_attributes
          with
          | None -> binding
          | Some attribute -> (
              let leads =
                take_gap_any_line ~after:attribute.attr_loc
                  ~before_cnum:binding.pvb_pat.ppat_loc.loc_start.pos_cnum
              in
              with_binding_markers "leadreactcomponent" leads binding)
        in
        (* A `let x : t = ...` binding's type is deliberately excluded
           from the candidate pool, so reuse lead_block_body on the value. *)
        let binding =
          match binding.Ppxlib.Parsetree.pvb_constraint with
          | Some (Pvc_constraint { typ; _ }) ->
              {
                binding with
                pvb_expr = lead_block_body ~after:typ.ptyp_loc binding.pvb_expr;
              }
          | Some (Pvc_coercion _) | None -> binding
        in
        match binding.Ppxlib.Parsetree.pvb_expr.pexp_desc with
        | Pexp_function (_ :: _ as params, constraint_, body)
          ->
            let rec split ~is_first (previous_end : Location.t) = function
              | [] -> []
              | (param : Ppxlib.Parsetree.function_param) :: rest -> (
                  match param.pparam_desc with
                  | Pparam_val (_, _, pattern) ->
                      let candidates =
                        take_gap_any_line ~after:previous_end
                          ~before_cnum:pattern.ppat_loc.loc_start.pos_cnum
                      in
                      let trailing, leading =
                        if is_first then ([], candidates)
                        else
                          List.partition
                            (fun (c : source_comment) ->
                              c.location.loc_start.pos_lnum
                              = previous_end.loc_end.pos_lnum)
                            candidates
                      in
                      let kind =
                        match (param.pparam_desc, is_first) with
                        | Pparam_val (_, Some _, _), true -> "leadparamdefault"
                        | Pparam_val (_, Some _, _), false -> "leadparamdefaultown"
                        | (Pparam_val (_, None, _) | Pparam_newtype _), true -> "lead"
                        | (Pparam_val (_, None, _) | Pparam_newtype _), false -> "leadparamown"
                      in
                      let param =
                        map_param_pattern (with_pat_markers kind leading) param
                      in
                      (trailing, param) :: split ~is_first:false pattern.ppat_loc rest
                  | Pparam_newtype _ ->
                      ([], param) :: split ~is_first:false previous_end rest)
            in
            let steps = split ~is_first:true binding.pvb_pat.ppat_loc params in
            (* A trailing comment must land after the default value
               (`~x=false, /* c */`), or it splits the parameter in two. *)
            let attach_trailing_markers
                (param : Ppxlib.Parsetree.function_param) trailing =
              match param.pparam_desc with
              | Pparam_val (label, Some default, pattern) ->
                  {
                    param with
                    pparam_desc =
                      Pparam_val
                        ( label,
                          Some (with_expr_markers "leadtrailingparam" trailing default),
                          pattern );
                  }
              | Pparam_val (_, None, _) | Pparam_newtype _ ->
                  map_param_pattern
                    (with_pat_markers "leadtrailingparam" trailing)
                    param
            in
            (* A step's trailing bucket is found before the next param, so
               it shifts onto the preceding one. *)
            let rec shift = function
              | [] -> []
              | [ (_, param) ] -> [ param ]
              | (_, param) :: ((next_trailing, _) :: _ as rest) ->
                  attach_trailing_markers param next_trailing :: shift rest
            in
            let params = shift steps in
            let constraint_, body =
              reason_return_type_constraint constraint_ body
            in
            let body =
              match body with
              | Pfunction_body inner ->
                  (* A param's ppat_loc stops before its default value, so
                     this gap is between the default (if any) and body. *)
                  let last_param_loc =
                    match (List.hd (List.rev params)).pparam_desc with
                    | Pparam_val (_, Some default, pattern) ->
                        if default.pexp_loc.loc_end.pos_cnum
                           > pattern.ppat_loc.loc_end.pos_cnum
                        then default.pexp_loc
                        else pattern.ppat_loc
                    | Pparam_val (_, None, pattern) -> pattern.ppat_loc
                    | Pparam_newtype id -> id.loc
                  in
                  Pfunction_body
                    (lead_block_body ~after:last_param_loc inner)
              | Pfunction_cases _ -> body
            in
            {
              binding with
              pvb_expr =
                {
                  binding.pvb_expr with
                  pexp_desc = Pexp_function (params, constraint_, body);
                };
            }
        | _ -> (
            match binding.pvb_constraint with
            | Some _ -> binding
            | None ->
                {
                  binding with
                  pvb_expr =
                    lead_block_body ~after:binding.pvb_pat.ppat_loc
                      binding.pvb_expr;
                })

      method! core_type type_ =
        let type_ = super#core_type type_ in
        match type_.ptyp_desc with
        | Ptyp_variant (first :: rest, closed, labels) ->
            let rest =
              lead_each ~after:first.prf_loc
                ~start:(fun (f : Ppxlib.Parsetree.row_field) -> f.prf_loc.loc_start.pos_cnum)
                ~finish:(fun (f : Ppxlib.Parsetree.row_field) -> f.prf_loc)
                ~mark:(with_row_field_markers "leadvariant") rest
            in
            { type_ with ptyp_desc = Ptyp_variant (first :: rest, closed, labels) }
        | _ -> type_

      method! constructor_declaration constructor =
        let constructor = super#constructor_declaration constructor in
        match constructor.pcd_args with
        | Pcstr_record fields ->
            {
              constructor with
              pcd_args =
                Pcstr_record
                  (lead_record_fields ~after:constructor.pcd_name.loc fields);
            }
        | Pcstr_tuple _ -> constructor

      (* Attributing the type's first param forces an invalid extra paren. *)
      method! type_declaration decl =
        let decl = super#type_declaration decl in
        let header_end =
          match List.rev decl.Ppxlib.Parsetree.ptype_params with
          | (last_param, _) :: _ -> last_param.Ppxlib.Parsetree.ptyp_loc
          | [] -> decl.ptype_name.loc
        in
        match decl.ptype_kind with
        | Ptype_variant (first :: rest) ->
            let variants =
              lead_each ~after:header_end
                ~start:(fun (c : Ppxlib.Parsetree.constructor_declaration) ->
                  c.pcd_loc.loc_start.pos_cnum)
                ~finish:(fun (c : Ppxlib.Parsetree.constructor_declaration) -> c.pcd_loc)
                ~mark:(with_constructor_markers "lead") (first :: rest)
            in
            { decl with ptype_kind = Ptype_variant variants }
        | Ptype_record fields ->
            {
              decl with
              ptype_kind =
                Ptype_record (lead_record_fields ~after:header_end fields);
            }
        | Ptype_abstract -> (
            match decl.ptype_manifest with
            | Some ({ ptyp_desc = Ptyp_variant (first :: rest, closed, labels); _ } as manifest)
              ->
                let first =
                  with_row_field_markers "leadvariant"
                    (take_gap ~after:header_end
                       ~before_cnum:first.prf_loc.loc_start.pos_cnum)
                    first
                in
                {
                  decl with
                  ptype_manifest =
                    Some
                      {
                        manifest with
                        ptyp_desc = Ptyp_variant (first :: rest, closed, labels);
                      };
                }
            | _ -> decl)
        | _ -> decl
    end
  in
  let ast = map_source mapper ast in
  let remaining_ids = List.map (fun (c : source_comment) -> c.id) !remaining in
  let consumed =
    List.filter
      (fun (c : source_comment) -> not (List.mem c.id remaining_ids))
      comments
  in
  (ast, !remaining, consumed)

let contains (location : Location.t) (comment : source_comment) =
  location.loc_start.pos_cnum <= comment.location.loc_start.pos_cnum
  && comment.location.loc_end.pos_cnum <= location.loc_end.pos_cnum

let location_width location =
  location.Location.loc_end.pos_cnum - location.Location.loc_start.pos_cnum

let pick ~location ~keep ~better candidates =
  List.fold_left
    (fun selected candidate ->
      let candidate_location = location candidate in
      if not (keep candidate_location) then selected
      else
        match selected with
        | Some previous when not (better candidate_location (location previous))
          ->
            selected
        | _ -> Some candidate)
    None candidates

let preserve_declaration_comments ~text ast comments =
  let remaining = ref comments in
  let take_trailing ?(separators = [ ' '; '\t'; ';'; ')' ]) (location : Location.t) =
    let start_at offset =
      List.find_opt
        (fun (comment : source_comment) ->
          comment.location.loc_start.pos_cnum = offset
          && comment.location.loc_start.pos_lnum = location.loc_end.pos_lnum)
        !remaining
    in
    let rec scan offset taken =
      if offset >= String.length text then List.rev taken
      else
        match text.[offset] with
        | separator when List.mem separator separators -> scan (offset + 1) taken
        | _ -> (
            match start_at offset with
            | Some comment ->
                remaining :=
                  List.filter
                    (fun (other : source_comment) -> other.id <> comment.id)
                    !remaining;
                scan comment.location.loc_end.pos_cnum (comment :: taken)
            | None -> List.rev taken)
    in
    scan location.loc_end.pos_cnum []
  in
  let mapper =
    object
      inherit Ppxlib.Ast_traverse.map as super

      method! constructor_declaration constructor =
        let constructor = super#constructor_declaration constructor in
        let taken = take_trailing constructor.pcd_loc in
        {
          constructor with
          pcd_attributes =
            constructor.pcd_attributes
            @ List.map (marker_attribute "trailingcomment") taken;
        }

      method! functor_parameter parameter =
        match super#functor_parameter parameter with
        | Named (name, module_type) ->
            let taken =
              take_trailing ~separators:[ ' '; '\t' ] module_type.pmty_loc
            in
            Named
              ( name,
                {
                  module_type with
                  pmty_attributes =
                    module_type.pmty_attributes
                    @ List.map (marker_attribute "comment") taken;
                } )
        | Unit -> Unit

      method! row_field field =
        let field = super#row_field field in
        let taken = take_trailing field.prf_loc in
        {
          field with
          prf_attributes =
            field.prf_attributes
            @ List.map (marker_attribute "trailingcomment") taken;
        }
    end
  in
  let ast = map_source mapper ast in
  (ast, !remaining)

let map_last f list =
  match List.rev list with
  | last :: rest -> Some (List.rev (f last :: rest))
  | [] -> None

let structure_item_attributes (item : Ppxlib.Parsetree.structure_item) =
  match item.pstr_desc with
  | Pstr_eval (_, attributes) | Pstr_extension (_, attributes) -> attributes
  | Pstr_value (_, binding :: _) -> binding.pvb_attributes
  | Pstr_primitive description -> description.pval_attributes
  | Pstr_type (_, declaration :: _) -> declaration.ptype_attributes
  | Pstr_typext extension -> extension.ptyext_attributes
  | Pstr_exception exception_ ->
      exception_.ptyexn_constructor.pext_attributes @ exception_.ptyexn_attributes
  | Pstr_module binding -> binding.pmb_attributes
  | Pstr_recmodule (binding :: _) -> binding.pmb_attributes
  | Pstr_modtype declaration -> declaration.pmtd_attributes
  | Pstr_open declaration -> declaration.popen_attributes
  | Pstr_include declaration -> declaration.pincl_attributes
  | _ -> []

let signature_item_attributes (item : Ppxlib.Parsetree.signature_item) =
  match item.psig_desc with
  | Psig_extension (_, attributes) -> attributes
  | Psig_value description -> description.pval_attributes
  | Psig_type (_, declaration :: _) | Psig_typesubst (declaration :: _) ->
      declaration.ptype_attributes
  | Psig_typext extension -> extension.ptyext_attributes
  | Psig_exception exception_ ->
      exception_.ptyexn_constructor.pext_attributes @ exception_.ptyexn_attributes
  | Psig_module declaration -> declaration.pmd_attributes
  | Psig_recmodule (declaration :: _) -> declaration.pmd_attributes
  | Psig_modtype declaration | Psig_modtypesubst declaration ->
      declaration.pmtd_attributes
  | Psig_open description -> description.popen_attributes
  | Psig_include description -> description.pincl_attributes
  | _ -> []

let item_body_location ~text ~comments (location : Location.t)
    (attributes : Ppxlib.Parsetree.attribute list) =
  let rec after_attributes offset =
    let offset = skip_blank_and_comments ~text ~comments offset in
    match
      List.find_opt
        (fun (attribute : Ppxlib.Parsetree.attribute) ->
          attribute.attr_loc.loc_start.pos_cnum = offset
          && attribute.attr_loc.loc_end.pos_cnum > offset)
        attributes
    with
    | Some attribute -> after_attributes attribute.attr_loc.loc_end.pos_cnum
    | None -> offset
  in
  let start = after_attributes location.loc_start.pos_cnum in
  { location with loc_start = { location.loc_start with pos_cnum = start } }

let preserve_item_comments ~text ~within_items ast comments =
  let all_comments = comments in
  let remaining = ref comments in
  let take scope ~bodies locations =
    let selected, rest =
      List.partition
        (fun comment ->
          let locations =
            if starts_own_line text comment then bodies else locations
          in
          Option.fold ~none:true
            ~some:(fun location -> contains location comment)
            scope
          && (within_items
             || not
                  (List.exists
                     (fun location -> contains location comment)
                     locations)))
        !remaining
    in
    remaining := rest;
    selected
  in
  let rec interleave ~attach_trailing location attribute comments = function
    | [] ->
        List.map (fun comment -> attribute (marker_attribute "comment" comment)) comments
    | item :: items ->
        let before, after =
          List.partition
            (fun comment ->
              comment.location.loc_start.pos_cnum
              < (location item).Location.loc_end.pos_cnum)
            comments
        in
        (* A same-line comment stays in place only if the item can carry a
           trailing attribute (a `let` binding's body). *)
        let item_end = (location item).Location.loc_end in
        let same_line comment =
          comment.location.loc_start.pos_lnum = item_end.pos_lnum
          && comment.location.loc_start.pos_cnum >= item_end.pos_cnum
          &&
          match items with
          | next :: _ ->
              comment.location.loc_start.pos_cnum < (location next).Location.loc_start.pos_cnum
          | [] -> true
        in
        let trailing, after = List.partition same_line after in
        let item, after =
          List.fold_left
            (fun (item, after) comment ->
              match attach_trailing item comment with
              | Some item -> (item, after)
              | None -> (item, after @ [ comment ]))
            (item, after) trailing
        in
        List.map (fun comment -> attribute (marker_attribute "comment" comment)) before
        @ (item :: interleave ~attach_trailing location attribute after items)
  in
  let mapper =
    object (self)
      inherit Ppxlib.Ast_traverse.map as super
      val mutable scope = None
      val mutable payload_structures = []
      method! attribute attribute = attribute

      method private scoped : 'a 'b. Location.t -> ('a -> 'b) -> 'a -> 'b =
        fun location f x ->
          let previous = scope in
          scope <- Some location;
          let result = f x in
          scope <- previous;
          result

      (* An extension payload's nested structure still owns its own comments. *)
      method! structure_item item =
        self#scoped item.pstr_loc super#structure_item item

      method! signature_item item =
        self#scoped item.psig_loc super#signature_item item

      method! expression expression =
        self#scoped expression.pexp_loc super#expression expression

      method! module_expr expression =
        self#scoped expression.pmod_loc super#module_expr expression

      method! module_type type_ =
        self#scoped type_.pmty_loc super#module_type type_

      method! payload payload =
        (match payload with
        | PStr items -> payload_structures <- items :: payload_structures
        | _ -> ());
        super#payload payload

      method! structure items =
        let is_payload = List.memq items payload_structures in
        let items = super#structure items in
        let location item = item.Ppxlib.Parsetree.pstr_loc in
        let body_location (item : Ppxlib.Parsetree.structure_item) =
          item_body_location ~text ~comments:all_comments item.pstr_loc
            (structure_item_attributes item)
        in
        if
          is_payload
          && List.exists
               (fun (item : Ppxlib.Parsetree.structure_item) ->
                 (match item.pstr_desc with Pstr_attribute _ -> false | _ -> true)
                 && (location item).Location.loc_start.pos_cnum < 0)
               items
        then items
        else
        let comments =
          take scope ~bodies:(List.map body_location items) (List.map location items)
        in
        let rec attach_trailing (item : Ppxlib.Parsetree.structure_item) comment =
          let add attributes = attributes @ [ marker_attribute "comment" comment ] in
          Option.map
            (fun pstr_desc -> { item with pstr_desc })
            (match item.pstr_desc with
            | Pstr_open d -> Some (Pstr_open { d with popen_attributes = add d.popen_attributes })
            | Pstr_include d -> Some (Pstr_include { d with pincl_attributes = add d.pincl_attributes })
            | Pstr_module b -> Some (Pstr_module { b with pmb_attributes = add b.pmb_attributes })
            | Pstr_modtype d -> Some (Pstr_modtype { d with pmtd_attributes = add d.pmtd_attributes })
            | Pstr_extension (({ txt = "melange_only"; _ } as name, PStr [ inner ]), attributes) ->
                Option.map
                  (fun inner -> Pstr_extension ((name, PStr [ inner ]), attributes))
                  (attach_trailing inner comment)
            | Pstr_value (recflag, bindings) ->
                Option.map
                  (fun bindings -> Pstr_value (recflag, bindings))
                  (map_last
                     (fun (b : Ppxlib.Parsetree.value_binding) ->
                       { b with pvb_expr = { b.pvb_expr with pexp_attributes = add b.pvb_expr.pexp_attributes } })
                     bindings)
            | Pstr_primitive d -> Some (Pstr_primitive { d with pval_attributes = add d.pval_attributes })
            | Pstr_exception e -> Some (Pstr_exception { e with ptyexn_attributes = add e.ptyexn_attributes })
            | Pstr_type (recflag, declarations) ->
                Option.map
                  (fun declarations -> Pstr_type (recflag, declarations))
                  (map_last
                     (fun (d : Ppxlib.Parsetree.type_declaration) ->
                       { d with ptype_attributes = add d.ptype_attributes })
                     declarations)
            | _ -> None)
        in
        interleave ~attach_trailing location Ppxlib.Ast_helper.Str.attribute
          comments items

      method! signature items =
        let items = super#signature items in
        let location item = item.Ppxlib.Parsetree.psig_loc in
        let body_location (item : Ppxlib.Parsetree.signature_item) =
          item_body_location ~text ~comments:all_comments item.psig_loc
            (signature_item_attributes item)
        in
        let comments =
          take scope ~bodies:(List.map body_location items) (List.map location items)
        in
        let attach_trailing (item : Ppxlib.Parsetree.signature_item) comment =
          let add attributes = attributes @ [ marker_attribute "comment" comment ] in
          Option.map
            (fun psig_desc -> { item with psig_desc })
            (match item.psig_desc with
            | Psig_open d -> Some (Psig_open { d with popen_attributes = add d.popen_attributes })
            | Psig_include d -> Some (Psig_include { d with pincl_attributes = add d.pincl_attributes })
            | Psig_module d -> Some (Psig_module { d with pmd_attributes = add d.pmd_attributes })
            | Psig_modtype d -> Some (Psig_modtype { d with pmtd_attributes = add d.pmtd_attributes })
            | Psig_value d -> Some (Psig_value { d with pval_attributes = add d.pval_attributes })
            | Psig_exception e -> Some (Psig_exception { e with ptyexn_attributes = add e.ptyexn_attributes })
            | Psig_type (recflag, declarations) ->
                Option.map
                  (fun declarations -> Psig_type (recflag, declarations))
                  (map_last
                     (fun (d : Ppxlib.Parsetree.type_declaration) ->
                       { d with ptype_attributes = add d.ptype_attributes })
                     declarations)
            | _ -> None)
        in
        interleave ~attach_trailing location Ppxlib.Ast_helper.Sig.attribute
          comments items
    end
  in
  let ast = map_source mapper ast in
  (ast, !remaining)

let target_location = function
  | Expression_target expression -> expression.Ppxlib.Parsetree.pexp_loc
  | Field_target field -> field.Ppxlib.Parsetree.pld_loc
  | Type_target type_ -> type_.Ppxlib.Parsetree.ptyp_loc
  | Pattern_target pattern -> pattern.Ppxlib.Parsetree.ppat_loc

(* These constraint types stay valid fallback candidates for a stray
   comment, but are never treated as the "next sibling" to lead instead. *)
let constraint_types_to_exclude source =
  let excluded = ref [] in
  (* A constraint type can nest further core_type nodes, so the whole
     subtree needs excluding, not just the outermost type. *)
  let sub_collector =
    object
      inherit Ppxlib.Ast_traverse.iter as super

      method! core_type type_ =
        excluded := type_ :: !excluded;
        super#core_type type_
    end
  in
  let exclude_type_subtree typ = sub_collector#core_type typ in
  let exclude_constraint = function
    | Pconstraint typ -> exclude_type_subtree typ
    | Pcoerce (ground, typ) ->
        exclude_type_subtree typ;
        (match ground with Some typ -> exclude_type_subtree typ | None -> ())
  in
  let collector =
    object
      inherit Ppxlib.Ast_traverse.iter as super

      method! value_binding binding =
        (match binding.Ppxlib.Parsetree.pvb_constraint with
        | Some (Pvc_constraint { typ; _ }) ->
            exclude_type_subtree typ
        | Some (Pvc_coercion { ground; coercion }) ->
            exclude_type_subtree coercion;
            (match ground with
            | Some typ -> exclude_type_subtree typ
            | None -> ())
        | None -> ());
        super#value_binding binding

      method! expression expression =
        (match expression.Ppxlib.Parsetree.pexp_desc with
        | Pexp_function (params, constraint_, _) ->
            Option.iter exclude_constraint constraint_;
            List.iter
              (fun (param : Ppxlib.Parsetree.function_param) ->
                match param.pparam_desc with
                | Pparam_val (_, _, { ppat_desc = Ppat_constraint (_, typ); _ }) ->
                    exclude_type_subtree typ
                | Pparam_val _ | Pparam_newtype _ -> ())
              params
        | _ -> ());
        super#expression expression
    end
  in
  iter_source collector source;
  !excluded

(* Pairs of adjacent labelled-parameter types in a .rei/external arrow
   chain, of adjacent object field types and of adjacent constructor
   argument types (None before the first):
   nearest_previous/nearest_next pick by position alone. *)
let sibling_type_pairs source =
  let pairs = ref [] and firsts = ref [] in
  let sibling previous typ =
    match previous with
    | Some previous -> pairs := (previous, typ) :: !pairs
    | None -> firsts := typ :: !firsts
  in
  let collector =
    object
      inherit Ppxlib.Ast_traverse.iter as super

      method! core_type type_ =
        (match type_.Ppxlib.Parsetree.ptyp_desc with
        | Ptyp_arrow (_, domain, ({ ptyp_desc = Ptyp_arrow (_, next_domain, _); _ } as codomain))
          ->
            pairs := (domain, next_domain) :: (domain, codomain) :: !pairs
        | Ptyp_object (fields, _) ->
            let field_type (field : Ppxlib.Parsetree.object_field) =
              match field.pof_desc with Otag (_, typ) -> Some typ | Oinherit _ -> None
            in
            ignore
              (List.fold_left
                 (fun previous field ->
                   match field_type field with
                   | Some typ ->
                       sibling previous typ;
                       Some typ
                   | None -> previous)
                 None fields)
        | _ -> ());
        super#core_type type_

      method! constructor_declaration constructor =
        (match constructor.pcd_args with
        | Pcstr_tuple arguments ->
            ignore
              (List.fold_left
                 (fun previous argument ->
                   sibling previous argument;
                   Some argument)
                 None arguments)
        | Pcstr_record _ -> ());
        super#constructor_declaration constructor
    end
  in
  iter_source collector source;
  (!pairs, !firsts)

let comment_candidates source (comment : source_comment) =
  let candidates = ref [] in
  let boundary = ref None in
  let collector =
    object (self)
      inherit Ppxlib.Ast_traverse.iter as super
      val mutable in_jsx = false
      val mutable in_list = false
      val mutable same_location_arguments = []
      method! attribute _ = ()

      method! case case =
        let location =
          {
            case.pc_rhs.pexp_loc with
            loc_start = case.pc_lhs.ppat_loc.loc_start;
          }
        in
        if contains location comment then boundary := Some location;
        super#case case

      method! expression expression =
        let previous_in_jsx = in_jsx in
        let previous_in_list = in_list in
        let is_list_constructor =
          match expression.pexp_desc with
          | Pexp_construct
              ({ txt = Lident ("[]" | "::"); _ }, _) ->
              true
          | _ -> false
        in
        (* A record's own fields are not list elements, even inside one:
           they stay candidates. *)
        let is_record =
          match expression.pexp_desc with Pexp_record _ -> true | _ -> false
        in
        in_list <- (in_list || is_list_constructor) && not is_record;
        let is_jsx = List.exists is_jsx_attribute expression.pexp_attributes in
        in_jsx <- in_jsx || is_jsx;
        let is_wrapper =
          match expression.pexp_desc with
          | Pexp_tuple _ | Pexp_poly _ -> true
          | _ -> false
        in
        if
          is_jsx
          || (not is_wrapper) && (not is_list_constructor)
        then candidates := Expression_target expression :: !candidates;
        (match expression.pexp_desc with
        | Pexp_apply (callee, arguments) when is_jsx ->
            (* The JSX printer omits the unit argument and list spine. *)
            candidates := Expression_target callee :: !candidates;
            List.iter
              (function
                | ( Nolabel,
                    {
                      Ppxlib.Parsetree.pexp_desc =
                        Pexp_construct
                          ({ txt = Lident "()"; _ }, None);
                      _;
                    } ) ->
                    ()
                | _, argument -> self#expression argument)
              arguments
        | _ -> super#expression expression);
        in_jsx <- previous_in_jsx;
        in_list <- previous_in_list

      method! label_declaration field =
        candidates := Field_target field :: !candidates;
        super#label_declaration field

      method! core_type type_ =
        candidates := Type_target type_ :: !candidates;
        super#core_type type_

      method! pattern pattern =
        (match pattern.ppat_desc with
        | Ppat_construct (_, Some (_, argument)) | Ppat_variant (_, Some argument)
          when argument.ppat_loc = pattern.ppat_loc ->
            same_location_arguments <- argument :: same_location_arguments
        | Ppat_construct
            ( { txt = Lident "::"; _ },
              Some (_, ({ ppat_desc = Ppat_tuple _; _ } as cells)) ) ->
            same_location_arguments <- cells :: same_location_arguments
        | _ -> ());
        if location_width pattern.ppat_loc > 0 && not (List.memq pattern same_location_arguments)
        then candidates := Pattern_target pattern :: !candidates;
        super#pattern pattern
    end
  in
  iter_source collector source;
  match !boundary with
  | None -> !candidates
  | Some boundary ->
      List.filter
        (fun target ->
          let location = target_location target in
          boundary.loc_start.pos_cnum <= location.loc_start.pos_cnum
          && location.loc_end.pos_cnum <= boundary.loc_end.pos_cnum)
        !candidates

let nearest_previous (comment : source_comment) candidates =
  pick ~location:target_location
    ~keep:(fun l -> l.Location.loc_end.pos_cnum <= comment.location.loc_start.pos_cnum)
    ~better:(fun l s ->
      l.loc_end.pos_cnum > s.loc_end.pos_cnum
      || (l.loc_end.pos_cnum = s.loc_end.pos_cnum
         && location_width l > location_width s))
    candidates

let nearest_next (comment : source_comment) candidates =
  pick ~location:target_location
    ~keep:(fun l -> l.Location.loc_start.pos_cnum >= comment.location.loc_end.pos_cnum)
    ~better:(fun l s ->
      l.loc_start.pos_cnum < s.loc_start.pos_cnum
      || (l.loc_start.pos_cnum = s.loc_start.pos_cnum
         && location_width l > location_width s))
    candidates

let nearest_containing (comment : source_comment) candidates =
  pick ~location:target_location
    ~keep:(fun l -> contains l comment)
    ~better:(fun l s -> location_width l < location_width s)
    candidates

let jsx_callees source =
  let callees = ref [] in
  let collector =
    object
      inherit Ppxlib.Ast_traverse.iter as super

      method! expression expression =
        (match expression.pexp_desc with
        | Pexp_apply (callee, _) when List.exists is_jsx_attribute expression.pexp_attributes ->
            callees := callee :: !callees
        | _ -> ());
        super#expression expression
    end
  in
  iter_source collector source;
  !callees

let jsx_children source =
  let children = ref [] in
  let rec spine (e : Ppxlib.Parsetree.expression) =
    match e.pexp_desc with
    | Pexp_construct ({ txt = Lident "::"; _ }, Some { pexp_desc = Pexp_tuple [ head; tail ]; _ }) ->
        children := head :: !children;
        spine tail
    | _ -> ()
  in
  let collector =
    object
      inherit Ppxlib.Ast_traverse.iter as super

      method! expression expression =
        (if List.exists is_jsx_attribute expression.pexp_attributes then
           match expression.pexp_desc with
           | Pexp_apply (_, arguments) ->
               List.iter
                 (function Ppxlib.Labelled "children", value -> spine value | _ -> ())
                 arguments
           | Pexp_construct _ -> spine expression
           | _ -> ());
        super#expression expression
    end
  in
  iter_source collector source;
  !children

let type_header_params source =
  let params = ref [] in
  let collector =
    object
      inherit Ppxlib.Ast_traverse.iter as super

      method! type_declaration declaration =
        List.iter
          (fun ((param : Ppxlib.Parsetree.core_type), _) ->
            match param.ptyp_desc with Ptyp_var _ -> params := param :: !params | _ -> ())
          declaration.ptype_params;
        super#type_declaration declaration
    end
  in
  iter_source collector source;
  !params

let leads_next_node text others (comment : source_comment) next =
  let start = comment.location.loc_end.pos_cnum in
  let next_start = (target_location next).loc_start.pos_cnum in
  next_start >= start
  && ((target_location next).loc_start.pos_lnum = comment.location.loc_end.pos_lnum
     || starts_own_line text comment)
  && Seq.for_all
       (fun offset ->
         offset_in_comment others offset
         ||
         match text.[offset] with
         | ' ' | '\t' | '\r' | '\n' | '(' | '[' | '{' | '|' -> true
         | _ -> false)
       (Seq.init (next_start - start) (fun i -> start + i))

(* Reusing a pattern or a punned prop value as a lead anchor misprints. *)
let unleadable_nodes source =
  let patterns = ref [] and values = ref [] in
  let collector =
    object
      inherit Ppxlib.Ast_traverse.iter as super

      method! value_binding binding =
        if has_locally_abstract_constraint binding then patterns := binding.pvb_pat :: !patterns;
        super#value_binding binding

      method! expression expression =
        (match expression.pexp_desc with
        | Pexp_apply (_, arguments) when List.exists is_jsx_attribute expression.pexp_attributes ->
            List.iter
              (fun (label, (value : Ppxlib.Parsetree.expression)) ->
                match (label, value.pexp_desc) with
                | ( (Ppxlib.Labelled name | Ppxlib.Optional name),
                    Pexp_ident { txt = Lident ident; _ } )
                  when String.equal name ident ->
                    values := value :: !values
                | _ -> ())
              arguments
        | Pexp_record (fields, _) ->
            List.iter
              (fun ((label : Ppxlib.Longident.t Location.loc), (value : Ppxlib.Parsetree.expression)) ->
                match (label.txt, value.pexp_desc) with
                | Lident name, Pexp_ident { txt = Lident ident; _ } when String.equal name ident ->
                    values := value :: !values
                | _ -> ())
              fields
        | _ -> ());
        super#expression expression
    end
  in
  iter_source collector source;
  (!patterns, !values)

let object_field_types source =
  let fields = ref [] in
  let collector =
    object
      inherit Ppxlib.Ast_traverse.iter as super

      method! core_type type_ =
        (match type_.Ppxlib.Parsetree.ptyp_desc with
        | Ptyp_object (object_fields, _) ->
            List.iter
              (fun (field : Ppxlib.Parsetree.object_field) ->
                match field.pof_desc with
                | Otag (label, typ) -> fields := (typ, label.loc) :: !fields
                | Oinherit _ -> ())
              object_fields
        | _ -> ());
        super#core_type type_
    end
  in
  iter_source collector source;
  !fields

let first_labelled_domains source =
  let domains = ref [] and continuations = ref [] in
  let collector =
    object
      inherit Ppxlib.Ast_traverse.iter as super

      method! core_type type_ =
        (match type_.Ppxlib.Parsetree.ptyp_desc with
        | Ptyp_arrow (label, domain, codomain) ->
            (match codomain.ptyp_desc with
            | Ptyp_arrow _ -> continuations := codomain :: !continuations
            | _ -> ());
            if label <> Nolabel && not (List.memq type_ !continuations) then
              domains := domain :: !domains
        | _ -> ());
        super#core_type type_
    end
  in
  iter_source collector source;
  !domains

let or_pattern_alternatives source =
  let alternatives = ref [] in
  let rec flatten (pattern : Ppxlib.Parsetree.pattern) =
    match pattern.ppat_desc with
    | Ppat_or (left, right) -> flatten left @ flatten right
    | _ -> [ pattern ]
  in
  let collector =
    object
      inherit Ppxlib.Ast_traverse.iter as super

      method! pattern pattern =
        (match (pattern.ppat_desc, flatten pattern) with
        | Ppat_or _, _ :: rest -> alternatives := rest @ !alternatives
        | _ -> ());
        super#pattern pattern
    end
  in
  iter_source collector source;
  !alternatives

let assign_nested_comments ~text ast (comments : source_comment list) =
  let or_alternatives = or_pattern_alternatives ast in
  let field_types = object_field_types ast in
  let first_domains = first_labelled_domains ast in
  let items = ref [] in
  let collector =
    object
      inherit Ppxlib.Ast_traverse.iter as super

      method! structure_item item =
        items := (item.pstr_loc, Implementation [ item ]) :: !items;
        super#structure_item item

      method! signature_item item =
        items := (item.psig_loc, Interface [ item ]) :: !items;
        super#signature_item item
    end
  in
  iter_source collector ast;
  let jsx_child_nodes = jsx_children ast in
  let assignments =
    comments
    |> List.filter_map (fun (comment : source_comment) ->
        let item =
          pick ~location:fst
            ~keep:(fun l -> contains l comment)
            ~better:(fun l s -> location_width l < location_width s)
            !items
        in
        Option.bind item (fun (_, item) ->
            let candidates = comment_candidates item comment in
            let excluded_types = constraint_types_to_exclude item in
            let type_pairs, first_types = sibling_type_pairs item in
            (* A same-line comment trails a type unless another type sits
               right after it on the same line, which it leads instead. *)
            let is_type_target = function
              | Type_target _ -> true
              | Expression_target _ | Field_target _ | Pattern_target _ -> false
            in
            let same_line_as_previous previous =
              (target_location previous).loc_end.pos_lnum
              = comment.location.loc_start.pos_lnum
            in
            let next_type_sibling_same_line () =
              match nearest_next comment candidates with
              | Some (Type_target next_type as next)
                when (target_location next).loc_start.pos_lnum
                     = comment.location.loc_end.pos_lnum
                     && not (List.memq next_type excluded_types) ->
                  Some next
              | Some _ | None -> None
            in
            (* An own-line comment leads the next type only when it's a
               genuine next parameter in the same .rei arrow chain, not
               merely the nearest type across an unrelated structure. *)
            let next_type_sibling_any_line previous_type =
              match nearest_next comment candidates with
              | Some (Type_target next_type as next)
                when (not (List.memq next_type excluded_types))
                     && List.exists
                          (fun (a, b) -> a == previous_type && b == next_type)
                          type_pairs ->
                  Some next
              | Some _ | None -> None
            in
            let jsx_callees = jsx_callees item in
            let is_jsx_child e =
              List.exists is_jsx_attribute e.Ppxlib.Parsetree.pexp_attributes
              && List.memq e jsx_child_nodes
            in
            let unleadable_patterns, unleadable_values = unleadable_nodes item in
            let header_params = type_header_params item in
            let is_header_param = function
              | Type_target type_ -> List.memq type_ header_params
              | Expression_target _ | Field_target _ | Pattern_target _ -> false
            in
            let header_param_target () =
              let closes_list =
                let rest =
                  String.sub text comment.location.loc_end.pos_cnum
                    (String.length text - comment.location.loc_end.pos_cnum)
                in
                match String.trim rest with
                | "" -> false
                | trimmed -> trimmed.[0] = ',' || trimmed.[0] = ')'
              in
              match (nearest_previous comment candidates, nearest_next comment candidates) with
              | Some previous, _ when is_header_param previous && closes_list -> Some previous
              | previous, Some next when is_header_param next && leads_next_node text comments comment next ->
                  (match previous with
                  | Some previous when is_header_param previous -> Some previous
                  | _ -> Some next)
              | _ -> None
            in
            let rec operand_to_lead (e : Ppxlib.Parsetree.expression) =
              match e.pexp_desc with
              | Pexp_apply
                  ( { pexp_desc = Pexp_ident { txt = Lident ("~-" | "~-." | "~+" | "~+."); _ }; _ },
                    [ (Nolabel, operand) ] ) ->
                  operand_to_lead operand
              | _ -> e
            in
            let first_in_block () =
              match nearest_containing comment candidates with
              | Some (Expression_target e as container)
                when (not (is_jsx_child e))
                     && (not (List.memq e jsx_callees))
                     && e.pexp_loc.loc_start.pos_cnum < comment.location.loc_start.pos_cnum
                     && Seq.for_all
                          (fun offset ->
                            List.exists
                              (fun (other : source_comment) ->
                                other.location.loc_start.pos_cnum <= offset
                                && offset < other.location.loc_end.pos_cnum)
                              comments
                            || match text.[offset] with
                               | ' ' | '\t' | '\r' | '\n' | '(' | '{' -> true
                               | _ -> false)
                          (Seq.init
                             (comment.location.loc_start.pos_cnum - e.pexp_loc.loc_start.pos_cnum)
                             (fun i -> e.pexp_loc.loc_start.pos_cnum + i))
                     && (match nearest_previous comment candidates with
                        | Some previous ->
                            (target_location previous).loc_end.pos_cnum
                            <= e.pexp_loc.loc_start.pos_cnum
                        | None -> true) ->
                  Some container
              | Some _ | None -> None
            in
            let after_jsx_sibling =
              match nearest_previous comment candidates with
              | Some (Expression_target e) ->
                  List.exists is_jsx_attribute e.pexp_attributes && starts_own_line text comment
              | Some _ | None -> false
            in
            let next_node_to_lead () =
              if after_jsx_sibling then None else
              match nearest_next comment candidates with
              | Some (Expression_target e as next)
                when (not (is_jsx_child e))
                     && (not (List.memq e jsx_callees))
                     && (not (List.memq e unleadable_values))
                     && (match e.pexp_desc with
                        | Pexp_let (_, binding :: _, _) -> not (has_locally_abstract_constraint binding)
                        | Pexp_ident { txt = Lident name; _ } ->
                            name <> "" && (Char.Ascii.is_letter name.[0] || name.[0] = '_')
                        | _ -> true)
                     && leads_next_node text comments comment next ->
                  Some (Expression_target (operand_to_lead e))
              | Some (Type_target typ as next)
                when (List.memq typ excluded_types || List.memq typ first_types)
                     && leads_next_node text comments comment next ->
                  Some next
              | Some (Pattern_target pattern as next)
                when (not (List.memq pattern unleadable_patterns))
                     && leads_next_node text comments comment next ->
                  Some next
              | Some _ | None -> first_in_block ()
            in
            let closes_block e =
              let stop = e.Ppxlib.Parsetree.pexp_loc.loc_end.pos_cnum in
              let skip = skip_blank_and_comments ~text ~comments in
              let brace = skip comment.location.loc_end.pos_cnum in
              brace < stop && text.[brace] = '}' && skip (brace + 1) >= stop
            in
            let enclosing_target =
              match nearest_containing comment candidates with
              | Some (Field_target field as container)
                when comment.location.loc_end.pos_cnum
                     <= field.pld_name.loc.loc_start.pos_cnum ->
                  Some container
              | Some (Expression_target e as container)
                when closes_block e
                     && (not (is_jsx_child e))
                     && (not (List.memq e jsx_callees))
                     && (match nearest_previous comment candidates with
                        | Some previous ->
                            (target_location previous).loc_end.pos_cnum
                            <= e.pexp_loc.loc_start.pos_cnum
                        | None -> true) ->
                  Some container
              | Some _ | None -> None
            in
            let inline_target = header_param_target () in
            let nearest_previous_node =
              match nearest_previous comment candidates with
              | Some (Pattern_target pattern) -> (
                  match nearest_containing comment candidates with
                  | Some container
                    when (target_location container).loc_start.pos_cnum
                         > pattern.ppat_loc.loc_end.pos_cnum ->
                      None
                  | Some _ | None -> Some (Pattern_target pattern))
              | previous -> previous
            in
            let target, leads_target =
              match inline_target with
              | Some target -> (Some target, false)
              | None when Option.is_some enclosing_target -> (enclosing_target, false)
              | None ->
              match nearest_previous_node with
              | Some previous when not (is_type_target previous) -> (
                  match next_node_to_lead () with
                  | Some next -> (Some next, true)
                  | None -> (
                      match (previous, nearest_next comment candidates) with
                      | Pattern_target _, Some next when leads_next_node text comments comment next -> (
                          match
                            nearest_previous comment
                              (List.filter
                                 (function Pattern_target _ -> false | _ -> true)
                                 candidates)
                          with
                          | Some earlier -> (Some earlier, false)
                          | None -> (Some next, false))
                      | _ -> (Some previous, false)))
              | Some previous when same_line_as_previous previous -> (
                  match next_type_sibling_same_line () with
                  | Some next -> (Some next, true)
                  | None -> (Some previous, false))
              | Some previous -> (
                  match previous with
                  | Type_target previous_type -> (
                      match next_type_sibling_any_line previous_type with
                      | Some next -> (Some next, true)
                      | None -> (Some previous, false))
                  | Expression_target _ | Field_target _ | Pattern_target _ -> (Some previous, false))
              | None -> (
                  match nearest_next comment candidates with
                  | Some target -> (
                      match next_node_to_lead () with
                      | Some lead -> (Some lead, true)
                      | None -> (
                          match target with
                          | Pattern_target pattern
                            when (not (List.memq pattern unleadable_patterns))
                                 && not
                                      (let before =
                                         String.trim (String.sub text 0 pattern.ppat_loc.loc_start.pos_cnum)
                                       in
                                       List.exists
                                         (fun keyword ->
                                           String.ends_with ~suffix:keyword before
                                           && String.length before - String.length keyword
                                              >= comment.location.loc_start.pos_cnum)
                                         [ "let"; "let rec"; "and" ]) ->
                              (Some target, true)
                          | Expression_target e
                            when not
                                   (is_jsx_child e
                                   || List.memq e jsx_callees
                                   || List.memq e unleadable_values) ->
                              (Some (Expression_target (operand_to_lead e)), true)
                          | Type_target typ
                            when (not (List.memq typ excluded_types))
                                 && List.memq typ first_types ->
                              (Some target, true)
                          | _ -> (Some target, false)))
                  | None -> (
                      match next_node_to_lead () with
                      | Some lead -> (Some lead, true)
                      | None -> (nearest_containing comment candidates, false)))
            in
            let target =
              match target with
              | Some (Type_target typ)
                when List.memq typ first_domains
                     && comment.location.loc_end.pos_cnum <= typ.ptyp_loc.loc_start.pos_cnum
                     && starts_own_line text comment ->
                  None
              | target -> target
            in
            Option.map
              (fun target ->
                let is_constraint_type =
                  match target with
                  | Type_target typ -> List.memq typ excluded_types
                  | Expression_target _ | Field_target _ | Pattern_target _ -> false
                in
                {
                  comment;
                  target;
                  leads_target;
                  inline = Option.is_some inline_target;
                  is_constraint_type;
                })
              target))
  in
  let ast =
    let markers_of is_target kind =
      List.filter_map
        (fun (assignment : comment_assignment) ->
          if is_target assignment.target && not assignment.inline then
            Some (marker_attribute (kind assignment) assignment.comment)
          else None)
        assignments
    in
    let mapper =
      object
        inherit Ppxlib.Ast_traverse.map as super

        method! expression expression =
          let markers =
            markers_of
              (function Expression_target t -> t == expression | _ -> false)
              (fun assignment ->
                if not assignment.leads_target then "comment"
                else if List.memq expression jsx_child_nodes then "leadchildcomment"
                else "leadnodecomment")
          in
          let expression = super#expression expression in
          {
            expression with
            pexp_attributes = expression.pexp_attributes @ markers;
          }

        method! pattern pattern =
          let markers =
            markers_of
              (function Pattern_target t -> t == pattern | _ -> false)
              (fun assignment ->
                if not assignment.leads_target then "comment"
                else if
                  List.memq pattern or_alternatives
                  && starts_own_line text assignment.comment
                then "leadaltcomment"
                else
                  match pattern.ppat_desc with
                  | Ppat_construct (_, Some _) | Ppat_variant (_, Some _) | Ppat_tuple _ -> "leadpatterncomment"
                  | _ -> "leadnodecomment")
          in
          let pattern = super#pattern pattern in
          { pattern with ppat_attributes = pattern.ppat_attributes @ markers }

        method! label_declaration field =
          let markers =
            markers_of
              (function Field_target t -> t == field | _ -> false)
              (fun _ -> "comment")
          in
          let field = super#label_declaration field in
          { field with pld_attributes = field.pld_attributes @ markers }

        method! type_declaration declaration =
          let rename (param : Ppxlib.Parsetree.core_type) =
            match param.ptyp_desc with
            | Ptyp_var name ->
                let texts =
                  List.filter_map
                    (fun (assignment : comment_assignment) ->
                      match assignment.target with
                      | Type_target t when assignment.inline && t == param ->
                          Some (print_comment_text assignment.comment.text)
                      | _ -> None)
                    assignments
                in
                if texts = [] then param
                else { param with ptyp_desc = Ptyp_var (String.concat " " (name :: texts)) }
            | _ -> param
          in
          super#type_declaration
            {
              declaration with
              ptype_params =
                List.map (fun (param, variance) -> (rename param, variance)) declaration.ptype_params;
            }

        method! core_type type_ =
          let markers =
            markers_of
              (function Type_target t -> t == type_ | _ -> false)
              (fun assignment ->
                if assignment.is_constraint_type then
                  if assignment.leads_target then "leadnodecomment" else "comment"
                else if
                  assignment.leads_target
                  && List.exists
                       (fun (typ, (label : Location.t)) ->
                         typ == type_
                         && assignment.comment.location.loc_end.pos_cnum
                            <= label.loc_start.pos_cnum)
                       field_types
                then "leadfieldcomment"
                else if assignment.leads_target then "leadtypecomment"
                else "typecomment")
          in
          let type_ = super#core_type type_ in
          { type_ with ptyp_attributes = type_.ptyp_attributes @ markers }
      end
    in
    map_source mapper ast
  in
  let assigned_ids =
    List.map
      (fun (assignment : comment_assignment) -> assignment.comment.id)
      assignments
  in
  let comments =
    List.filter
      (fun (comment : source_comment) -> not (List.mem comment.id assigned_ids))
      comments
  in
  let inline_ids =
    List.filter_map
      (fun (assignment : comment_assignment) ->
        if assignment.inline then Some assignment.comment.id else None)
      assignments
  in
  (ast, comments, inline_ids)

let has_blank_gap ~comments (loc_end : Lexing.position)
    (loc_start : Lexing.position) =
  let gap_first_line = loc_end.pos_lnum + 1 in
  let gap_last_line = loc_start.pos_lnum - 1 in
  gap_last_line >= gap_first_line
  &&
  let comment_lines =
    List.fold_left
      (fun total (comment : source_comment) ->
        if
          comment.location.loc_start.pos_cnum >= loc_end.pos_cnum
          && comment.location.loc_end.pos_cnum <= loc_start.pos_cnum
        then
          let first = max comment.location.loc_start.pos_lnum gap_first_line in
          let last = min comment.location.loc_end.pos_lnum gap_last_line in
          total + max 0 (last - first + 1)
        else total)
      0 comments
  in
  gap_last_line - gap_first_line + 1 > comment_lines

let lex_tokens =
  let last = ref ("", []) in
  fun source ->
    let last_source, last_tokens = !last in
    if source == last_source then last_tokens
    else
      let lexbuf = Lexing.from_string source in
      Mlx_ast.Lexer.init ();
      let rec go acc =
        let token = Mlx_ast.Lexer.token lexbuf in
        let located = (token, Lexing.lexeme_start lexbuf, Lexing.lexeme_end lexbuf) in
        match token with Mlx_ast.Parser.EOF -> List.rev acc | _ -> go (located :: acc)
      in
      let tokens = go [] in
      last := (source, tokens);
      tokens

(* mark_blank_item_lines must run before preserve_item_comments (whose
   comment items have no location); mark_blank_expr_lines must run after
   the comment passes, or its wrapper steals a comment's attachment node. *)
let blank_item_marker_prefix = "reason_to_mlx.blank_item_"
let blank_expr_marker_prefix = "r2m_blank_expr_"

let blank_item_marker_attribute ~loc id : Ppxlib.Parsetree.attribute =
  let name = { Ppxlib.Location.txt = blank_item_marker_prefix ^ string_of_int id; loc } in
  Ppxlib.Ast_helper.Attr.mk ~loc name (PStr [])

let zero_width_loc (position : Lexing.position) : Location.t =
  { Location.loc_start = position; loc_end = position; loc_ghost = true }

let intervening_comments comments (loc_end : Lexing.position)
    (loc_start : Lexing.position) =
  comments
  |> List.filter (fun (comment : source_comment) ->
      comment.location.loc_start.pos_cnum >= loc_end.pos_cnum
      && comment.location.loc_end.pos_cnum <= loc_start.pos_cnum)
  |> List.sort (fun (a : source_comment) (b : source_comment) ->
      compare a.location.loc_start.pos_cnum b.location.loc_start.pos_cnum)

let blank_item_marker_locations ?(after_first_comment = false) comments
    (loc_end : Lexing.position) (loc_start : Lexing.position) =
  let sorted = intervening_comments comments loc_end loc_start in
  let gap_starts =
    loc_end :: List.map (fun (c : source_comment) -> c.location.loc_end) sorted
  in
  let gap_ends =
    List.map (fun (c : source_comment) -> c.location.loc_start) sorted
    @ [ loc_start ]
  in
  List.combine gap_starts gap_ends
  |> List.mapi (fun index (gap_start, gap_end) ->
      if not (has_blank_gap ~comments gap_start gap_end) then []
      else if index = 0 then if after_first_comment then [] else [ Location.none ]
      else [ zero_width_loc gap_start ])
  |> List.concat

let mark_blank_item_lines comments =
  let next_id = ref 0 in
  let markers_between ?after_first_comment loc_end loc_start =
    blank_item_marker_locations ?after_first_comment comments loc_end loc_start
    |> List.map (fun loc ->
        incr next_id;
        (loc, blank_item_marker_attribute ~loc !next_id))
  in
  (* Str.attribute/Sig.attribute default to Location.none unless given a
     loc; the marker needs its real loc or sorting breaks. *)
  let insert_markers :
        'a. 'a list -> loc:('a -> Location.t) ->
        wrap:(Location.t -> Ppxlib.Parsetree.attribute -> 'a) -> 'a list =
   fun items ~loc ~wrap ->
    let rec go = function
      | a :: (b :: _ as rest) ->
          let markers =
            markers_between (loc a).loc_end (loc b).loc_start
            |> List.map (fun (marker_loc, attr) -> wrap marker_loc attr)
          in
          a :: (markers @ go rest)
      | items -> items
    in
    go items
  in
  let file_start = { Lexing.dummy_pos with pos_lnum = 0; pos_cnum = 0 } in
  let insert_header_markers :
        'a. 'a list -> loc:('a -> Location.t) ->
        wrap:(Location.t -> Ppxlib.Parsetree.attribute -> 'a) -> 'a list =
   fun items ~loc ~wrap ->
    match items with
    | first :: _ ->
        let markers =
          markers_between ~after_first_comment:true file_start (loc first).loc_start
        in
        List.map (fun (marker_loc, attr) -> wrap marker_loc attr) markers @ items
    | [] -> items
  in
  let at_top = ref true in
  object
    inherit Ppxlib.Ast_traverse.map as super
    method marker_count = !next_id

    method! structure items =
      let top = !at_top in
      at_top := false;
      let items = super#structure items in
      let loc (i : Ppxlib.Parsetree.structure_item) = i.pstr_loc in
      let wrap loc attr = Ppxlib.Ast_helper.Str.attribute ~loc attr in
      let items = insert_markers items ~loc ~wrap in
      if top then insert_header_markers items ~loc ~wrap else items

    method! signature items =
      let top = !at_top in
      at_top := false;
      let items = super#signature items in
      let loc (i : Ppxlib.Parsetree.signature_item) = i.psig_loc in
      let wrap loc attr = Ppxlib.Ast_helper.Sig.attribute ~loc attr in
      let items = insert_markers items ~loc ~wrap in
      if top then insert_header_markers items ~loc ~wrap else items
  end

let mark_blank_expr_lines comments =
  let next_id = ref 0 in
  let marker ~loc =
    incr next_id;
    { Ppxlib.Location.txt = blank_expr_marker_prefix ^ string_of_int !next_id; loc }
  in
  let wrap_blank_let ~(anchor : Location.t) body =
    let loc = anchor in
    let binding =
      Ppxlib.Ast_helper.Vb.mk ~loc (Ppxlib.Ast_helper.Pat.var ~loc (marker ~loc))
        (Ppxlib.Ast_helper.Exp.construct ~loc
           { Ppxlib.Location.txt = Lident "()"; loc }
           None)
    in
    Ppxlib.Ast_helper.Exp.let_ ~loc Nonrecursive [ binding ] body
  in
  let wrap_blank_sequence ~(anchor : Location.t) second =
    let loc = anchor in
    let name = marker ~loc in
    Ppxlib.Ast_helper.Exp.sequence ~loc
      (Ppxlib.Ast_helper.Exp.ident ~loc { name with txt = Lident name.txt })
      second
  in
  let mark_body ~(anchor : Location.t) (body : Ppxlib.Parsetree.expression) =
    if has_blank_gap ~comments anchor.loc_end body.pexp_loc.loc_start then
      wrap_blank_let ~anchor body
    else body
  in
  object
    inherit Ppxlib.Ast_traverse.map as super
    method marker_count = !next_id

    method! expression expression =
      let expression = super#expression expression in
      match expression.Ppxlib.Parsetree.pexp_desc with
      | Pexp_let (recflag, bindings, body) ->
          let anchor = (List.hd (List.rev bindings)).pvb_expr.pexp_loc in
          { expression with pexp_desc = Pexp_let (recflag, bindings, mark_body ~anchor body) }
      | Pexp_letop ({ let_; ands; body } as letop) ->
          let anchor = (List.hd (List.rev (let_ :: ands))).pbop_exp.pexp_loc in
          {
            expression with
            pexp_desc = Pexp_letop { letop with body = mark_body ~anchor body };
          }
      | Pexp_sequence (first, second) ->
          let anchor = first.Ppxlib.Parsetree.pexp_loc in
          if has_blank_gap ~comments anchor.loc_end second.pexp_loc.loc_start then
            {
              expression with
              pexp_desc = Pexp_sequence (first, wrap_blank_sequence ~anchor second);
            }
          else expression
      | _ -> expression
  end

let marker_id ~prefix name =
  if String.starts_with ~prefix name then
    int_of_string_opt
      (String.sub name (String.length prefix) (String.length name - String.length prefix))
  else None

let marker_at ~opening : Mlx_ast.Parser.(token * int * int) list -> _ = function
  | (token, start_offset, _)
    :: (LIDENT namespace, _, _)
    :: (DOT, _, _)
    :: (LIDENT name, _, _)
    :: (RBRACKET, _, end_offset)
    :: rest
    when token = opening ->
      Some (namespace ^ "." ^ name, start_offset, end_offset, rest)
  | _ -> None

let collect_blank_marker_spans tokens =
  let open Mlx_ast.Parser in
  let rec go tokens item_spans expr_spans =
    match marker_at ~opening:LBRACKETATATAT tokens with
    | Some (name, start_offset, end_offset, rest) -> (
        match marker_id ~prefix:blank_item_marker_prefix name with
        | Some id -> go rest ((id, start_offset, end_offset) :: item_spans) expr_spans
        | None -> go rest item_spans expr_spans)
    | None ->
    match tokens with
    | (LET, start_offset, _)
      :: (LIDENT name, _, _)
      :: (EQUAL, _, _)
      :: (LPAREN, _, _)
      :: (RPAREN, _, _)
      :: (IN, _, end_offset)
      :: rest -> (
        match marker_id ~prefix:blank_expr_marker_prefix name with
        | Some id -> go rest item_spans ((id, start_offset, end_offset) :: expr_spans)
        | None -> go rest item_spans expr_spans)
    | (LIDENT name, start_offset, _) :: (SEMI, _, end_offset) :: rest -> (
        match marker_id ~prefix:blank_expr_marker_prefix name with
        | Some id -> go rest item_spans ((id, start_offset, end_offset) :: expr_spans)
        | None -> go rest item_spans expr_spans)
    | _ :: rest -> go rest item_spans expr_spans
    | [] -> (item_spans, expr_spans)
  in
  go tokens [] []

let widen_whitespace source ~start ~stop =
  (blank_start source start, blank_end source stop)

let check_blank_markers_found ~kind count spans =
  let found = List.map (fun (id, _, _) -> id) spans in
  for id = 1 to count do
    if not (List.mem id found) then
      failwith ("missing blank-line " ^ kind ^ " marker " ^ string_of_int id)
  done

let apply_blank_marker_spans source spans =
  let widened =
    List.map (fun (_, start, stop) -> widen_whitespace source ~start ~stop) spans
    |> List.sort compare
  in
  let buffer = Buffer.create (String.length source) in
  let cursor =
    List.fold_left
      (fun cursor (start, stop) ->
        Buffer.add_substring buffer source cursor (start - cursor);
        Buffer.add_string buffer "\n\n";
        stop)
      0 widened
  in
  Buffer.add_substring buffer source cursor (String.length source - cursor);
  Buffer.contents buffer

let scrub_blank_markers source ~item_marker_count ~expr_marker_count =
  let item_spans, expr_spans = collect_blank_marker_spans (lex_tokens source) in
  check_blank_markers_found ~kind:"item" item_marker_count item_spans;
  check_blank_markers_found ~kind:"expression" expr_marker_count expr_spans;
  apply_blank_marker_spans source (item_spans @ expr_spans)

let print_documentation_comment text =
  if String.equal text "" then "(**)"
  else
    let text = escape_ocaml_comment text in
    let prefix = if text.[0] = ')' then " " else "" in
    let suffix = if text.[String.length text - 1] = '(' then " " else "" in
    "(**" ^ prefix ^ text ^ suffix ^ "*)"

(* Apply edits against original offsets so earlier ones don't shift later.
   An edit is (start, stop, replacement); an insert has start = stop. *)
let apply_edits source edits =
  let buffer = Buffer.create (String.length source) in
  let cursor =
    List.fold_left
      (fun cursor (start_offset, end_offset, replacement) ->
        Buffer.add_substring buffer source cursor (start_offset - cursor);
        Buffer.add_string buffer replacement;
        end_offset)
      0
      (List.stable_sort (fun (a, _, _) (b, _, _) -> compare a b) edits)
  in
  Buffer.add_substring buffer source cursor (String.length source - cursor);
  Buffer.contents buffer

(* The placeholder is plain ASCII, so Pprintast's `%S` quoting reproduces
   it verbatim: exactly one occurrence to find. *)
let restore_raw_string_literal source (placeholder, raw) =
  let pattern = Printf.sprintf "%S" placeholder in
  match String.find_first ~sub:pattern source with
  | None -> failwith ("missing raw string literal placeholder " ^ placeholder)
  | Some start_offset ->
      apply_edits source
        [ (start_offset, start_offset + String.length pattern, "\"" ^ raw ^ "\"") ]

let find_marker ?(opening = Mlx_ast.Parser.LBRACKETAT) tokens marker =
  let rec find tokens =
    match marker_at ~opening tokens with
    | Some (name, start_offset, end_offset, _) when String.equal name marker ->
        Some (start_offset, end_offset)
    | _ -> ( match tokens with _ :: rest -> find rest | [] -> None)
  in
  find tokens

let tokens_around tokens ~start_offset ~end_offset =
  ( List.rev
      (List.filter (fun (_, offset, _) -> offset < start_offset) tokens),
    List.filter (fun (_, offset, _) -> offset >= end_offset) tokens )

let around_marker source marker =
  let tokens = lex_tokens source in
  find_marker tokens marker
  |> Option.map (fun (start_offset, end_offset) ->
      let before, after = tokens_around tokens ~start_offset ~end_offset in
      (start_offset, end_offset, before, after))

let scan_back_unnested ?(skip = fun _ -> None) found tokens =
  let open Mlx_ast.Parser in
  let rec go depth tokens =
    match skip tokens with
    | Some rest -> go depth rest
    | None -> (
        match tokens with
        | [] -> None
        | (RPAREN, _, _) :: rest -> go (depth + 1) rest
        | (LPAREN, _, _) :: rest -> go (max 0 (depth - 1)) rest
        | _ :: rest -> (
            match if depth = 0 then found tokens else None with
            | Some _ as result -> result
            | None -> go depth rest))
  in
  go 0 tokens

let replace_marker_attribute ?opening source marker ~replacement =
  find_marker ?opening (lex_tokens source) marker
  |> Option.map (fun (start_offset, end_offset) ->
      apply_edits source [ (start_offset, end_offset, replacement) ])

let replace_trailing_marker_attribute ?opening source marker ~replacement =
  find_marker ?opening (lex_tokens source) marker
  |> Option.map (fun (start_offset, end_offset) ->
      let ends_line =
        match
          String.find_first_index
            (fun char -> char = '\n' || not (Char.Ascii.is_white char))
            ~start:end_offset source
        with
        | None -> true
        | Some offset -> source.[offset] = '\n'
      in
      let break = if ends_line then "" else "\n" in
      apply_edits source
        [ (blank_start source start_offset, end_offset, " " ^ replacement ^ break) ])

(* The inner of two extra parens the printer adds is load-bearing for a
   function type used as a labelled argument's type (`?x:(unit -> unit)
   -> ...`): stripping it would split one parameter into two. *)
let replace_type_comment_marker source marker ~replacement =
  let open Mlx_ast.Parser in
  let all_tokens = lex_tokens source in
  around_marker source marker
  |> Option.map (fun (marker_start, marker_end, before_marker, after_marker) ->
      let rec matching_open depth = function
        | [] -> None
        | (RPAREN, _, _) :: rest -> matching_open (depth + 1) rest
        | (LPAREN, open_start, open_end) :: rest ->
            if depth = 0 then Some (open_start, open_end, rest)
            else matching_open (depth - 1) rest
        | _ :: rest -> matching_open depth rest
      in
      (* A bare top-level `->` sits at paren depth 0; a further paren the
         type holds of its own (`React.ref(unit -> unit)`'s argument)
         pushes its arrow to depth 1, so it doesn't count. *)
      let has_own_top_level_arrow ~start_offset ~end_offset =
        let rec go depth = function
          | [] -> false
          | (LPAREN, _, _) :: rest -> go (depth + 1) rest
          | (RPAREN, _, _) :: rest -> go (depth - 1) rest
          | (MINUSGREATER, _, _) :: _ when depth = 0 -> true
          | _ :: rest -> go depth rest
        in
        all_tokens
        |> List.filter (fun (_, token_start, _) ->
            token_start >= start_offset && token_start < end_offset)
        |> go 0
      in
      let redundant_parens =
        match (before_marker, after_marker) with
        | ( (RPAREN, inner_close_start, inner_close_end) :: before_rest,
            (RPAREN, outer_close_start, outer_close_end) :: _ ) -> (
            match matching_open 0 before_rest with
            | Some
                ( inner_open_start,
                  inner_open_end,
                  (LPAREN, outer_open_start, outer_open_end) :: _ ) ->
                let inner_spans =
                  if
                    has_own_top_level_arrow ~start_offset:inner_open_end
                      ~end_offset:inner_close_start
                  then []
                  else
                    [
                      (inner_open_start, inner_open_end);
                      (inner_close_start, inner_close_end);
                    ]
                in
                (outer_open_start, outer_open_end)
                :: (outer_close_start, outer_close_end)
                :: inner_spans
            | Some _ | None -> [])
        | _ -> []
      in
      apply_edits source
        ((marker_start, marker_end, replacement)
        :: List.map (fun (start_offset, end_offset) -> (start_offset, end_offset, ""))
             redundant_parens))

let replace_node_comment_marker_as_lead ~inside ~constructor source marker ~replacement =
  let open Mlx_ast.Parser in
  let all_tokens = lex_tokens source in
  Option.bind (around_marker source marker) (fun (marker_start, marker_end, before_marker, _) ->
      let rec constructor_start start = function
        | (UIDENT _, _, _) :: (BACKQUOTE, tag_start, _) :: _
        | (LIDENT _, _, _) :: (BACKQUOTE, tag_start, _) :: _ ->
            tag_start
        | (UIDENT _, name_start, _) :: (DOT, _, _) :: rest -> constructor_start name_start rest
        | (UIDENT _, name_start, _) :: _ -> name_start
        | _ -> start
      in
      let rec enclosing_open depth = function
        | (RPAREN, _, _) :: rest -> enclosing_open (depth + 1) rest
        | (LPAREN, open_start, open_end) :: rest ->
            if depth > 0 then enclosing_open (depth - 1) rest
            else if inside then
              Some
                (match List.find_opt (fun (_, offset, _) -> offset >= open_end) all_tokens with
                | Some (_, offset, _) -> offset
                | None -> open_end)
            else if constructor then Some (constructor_start open_start rest)
            else Some open_start
        | _ :: rest -> enclosing_open depth rest
        | [] -> None
      in
      Option.map
        (fun insert_at ->
          apply_edits source
            [
              (marker_start, marker_end, "");
              (insert_at, insert_at, replacement ^ " ");
            ])
        (enclosing_open 0 before_marker))

let find_lead_marker_target ?(skip = fun _ -> false) ?(through_parens = false)
    ?(fallback_style = `Inline) source marker ~stop_token =
  let open Mlx_ast.Parser in
  around_marker source marker
  |> Option.map (fun (marker_start, marker_end, before_marker, _) ->
      (* An attribute on a pattern can add extra parens; track paren depth. *)
      let rec scan_back depth fallback = function
        | [] -> fallback
        | (token, start_offset, end_offset) :: rest -> (
            match token with
            | RPAREN when Option.is_some fallback -> fallback
            | RPAREN -> scan_back (depth + 1) fallback rest
            | LPAREN when depth > 0 -> scan_back (depth - 1) fallback rest
            | LPAREN when through_parens -> scan_back depth fallback rest
            | LPAREN when fallback = None ->
                scan_back depth (Some (start_offset, fallback_style)) rest
            | LPAREN -> fallback
            | _ when depth > 0 -> scan_back depth fallback rest
            | REC -> scan_back depth None rest
            | _ when skip token -> scan_back depth None rest
            | _ -> (
                match stop_token token with
                | Some (`Before, style) -> Some (start_offset, style)
                | Some (`After, style) -> Some (end_offset, style)
                | None -> (
                    match fallback with
                    | Some _ -> fallback
                    | None -> scan_back depth fallback rest)))
      in
      let introducer_offset, style =
        Option.value (scan_back 0 None before_marker)
          ~default:(marker_start, `Own_line)
      in
      (marker_start, marker_end, introducer_offset, style, []))

(* A record pattern field's value carries the marker, in parens the printer
   adds; the comment leads the field, so the target is the label before `=`. *)
let find_lead_pattern_field_marker_target source marker =
  let open Mlx_ast.Parser in
  Option.bind (around_marker source marker)
    (fun (marker_start, marker_end, before, _) ->
      let rec module_path start = function
        | (DOT, _, _) :: (UIDENT _, path_start, _) :: rest -> module_path path_start rest
        | _ -> start
      in
      scan_back_unnested
        (function
          | (EQUAL, _, _) :: (LIDENT _, label_start, _) :: rest ->
              Some (marker_start, marker_end, module_path label_start rest, `Own_line, [])
          | _ -> None)
        before)

(* The printer wraps an attributed `[]` as `(([])[@marker])`; both paren
   pairs are redundant once the marker is gone and must be stripped, or a
   leftover paren confuses the next pass's comment placement. *)
let find_lead_list_empty_marker_target source marker =
  let open Mlx_ast.Parser in
  Option.bind (around_marker source marker)
    (fun (marker_start, marker_end, before, after) ->
      match (before, after) with
      | ( (RPAREN, inner_rparen_start, inner_rparen_end)
          :: (RBRACKET, _, _)
          :: (LBRACKET, _, bracket_end)
          :: (LPAREN, inner_lparen_start, inner_lparen_end)
          :: (LPAREN, outer_lparen_start, outer_lparen_end)
          :: _,
          (RPAREN, outer_rparen_start, outer_rparen_end) :: _ ) ->
          Some
            ( marker_start,
              marker_end,
              bracket_end,
              `Inline,
              [
                (inner_lparen_start, inner_lparen_end);
                (inner_rparen_start, inner_rparen_end);
                (outer_lparen_start, outer_lparen_end);
                (outer_rparen_start, outer_rparen_end);
              ] )
      | _ -> None)

(* The marker's own position is already where the trailing comment
   belongs; no stop-token scan needed. *)
let find_lead_trailing_param_marker_target source marker =
  find_marker (lex_tokens source) marker
  |> Option.map (fun (marker_start, marker_end) ->
      (marker_start, marker_end, marker_start, `Inline, []))

(* The right operand of an infix operator carries the marker; the comment
   goes on its own line before the operator, the first token left of the
   operand's own parens. *)
let find_lead_operator_marker_target source marker =
  let open Mlx_ast.Parser in
  Option.bind (around_marker source marker)
    (fun (marker_start, marker_end, before, _) ->
      scan_back_unnested
        ~skip:(function
          | (RBRACKET, _, _)
            :: (LIDENT _, _, _)
            :: (DOT, _, _)
            :: (LIDENT _, _, _)
            :: (LBRACKETAT, _, _)
            :: rest ->
              Some rest
          | _ -> None)
        (function
          | (_, operator_start, _) :: _ ->
              Some (marker_start, marker_end, operator_start, `Own_line, [])
          | [] -> None)
        before)

(* The target is the nearest react.component-equivalent attribute after
   the marker, still pre-move (normalize_reason_ast hasn't run yet). *)
let find_lead_react_component_marker_target source marker =
  let open Mlx_ast.Parser in
  Option.bind (around_marker source marker)
    (fun (marker_start, marker_end, _, after_marker) ->
      let rec collect_dotted_name acc = function
        | (LIDENT part, _, _) :: (DOT, _, _) :: rest ->
            collect_dotted_name (part :: acc) rest
        | (LIDENT part, _, _) :: (RBRACKET, close_start, _) :: _ ->
            Some (String.concat "." (List.rev (part :: acc)), close_start)
        | _ -> None
      in
      let rec find_attribute = function
        | (LBRACKETAT, _, _) :: rest | (LBRACKETATAT, _, _) :: rest -> (
            match collect_dotted_name [] rest with
            | Some (name, close_start)
              when is_react_component_attribute_name name ->
                Some close_start
            | Some _ | None -> find_attribute rest)
        | _ :: rest -> find_attribute rest
        | [] -> None
      in
      Option.map
        (fun insert_offset ->
          (marker_start, marker_end, insert_offset, `Inline, []))
        (find_attribute after_marker))

(* A case or binding needs its own line to lead; a parameter stays inline. *)
let lead_stop_token (token : Mlx_ast.Parser.token) =
  match token with
  | BAR | LET | AND -> Some (`Before, `Own_line)
  | TILDE | QUESTION | LABEL _ | OPTLABEL _ ->
      (* Label tokens already include the tilde or question mark. *)
      Some (`Before, `Inline)
  | _ -> None

let lead_own_line_stop_token token =
  match lead_stop_token token with
  | Some (`Before, `Inline) -> Some (`Before, `Own_line)
  | stop -> stop

let own_line_after (tokens : Mlx_ast.Parser.token list) token =
  if List.mem token tokens then Some (`After, `Own_line) else None

let lead_list_stop_token = own_line_after [ SEMI; COMMA; LBRACKET; LBRACE ]

(* A record field's comment goes before its label, so the label, its path
   and the `=` are walked over instead of taking the value's paren. *)
let is_record_field_label_token (token : Mlx_ast.Parser.token) =
  match token with EQUAL | LIDENT _ | UIDENT _ | DOT -> true | _ -> false

let lead_record_field_stop_token =
  own_line_after [ SEMI; COMMA; LBRACE; WITH ]

(* Each marker kind finds its introducer by a different token: a let-chain
   body by `in`, `=` or `;`, a pipe stage by the operator, a record's first
   field by the opening brace, list and record elements by the prior
   separator, a case body by the case's arrow. *)
let lead_variant_stop_token (token : Mlx_ast.Parser.token) =
  match token with
  | BAR -> Some (`Before, `Own_line)
  | LBRACKET -> Some (`After, `Own_line)
  | _ -> None

let lead_marker_kinds =
  let scan ?skip ?through_parens ?fallback_style kind stop_token =
    ( kind,
      fun source marker ->
        find_lead_marker_target ?skip ?through_parens ?fallback_style source
          marker ~stop_token )
  in
  [
    ("leadlistempty", find_lead_list_empty_marker_target);
    ("leadpatternfield", find_lead_pattern_field_marker_target);
    ("leadtrailingparam", find_lead_trailing_param_marker_target);
    ("leadoperator", find_lead_operator_marker_target);
    ("leadreactcomponent", find_lead_react_component_marker_target);
    scan "lead" lead_stop_token;
    scan "leadin" (own_line_after [ IN; EQUAL; THEN; ELSE; DO; SEMI ]);
    scan "leadarg" lead_stop_token;
    scan "leadargown" lead_stop_token;
    scan "leadguard" (fun token ->
        if token = Mlx_ast.Parser.WHEN then Some (`Before, `Inline) else None);
    scan "leadvalue" (function
      | Mlx_ast.Parser.LABEL _ | OPTLABEL _ -> Some (`After, `Inline)
      | _ -> None);
    scan "leadfield" (own_line_after [ LBRACE ]);
    scan "leadlist" lead_list_stop_token;
    scan "leadvariant" lead_variant_stop_token;
    scan "leadcasebody" (own_line_after [ MINUSGREATER ]);
    scan ~through_parens:true "leadparamdefault" lead_stop_token;
    scan ~through_parens:true "leadparamdefaultown" lead_own_line_stop_token;
    scan ~fallback_style:`Own_line "leadparamown" lead_own_line_stop_token;
    scan ~skip:is_record_field_label_token "leadrecordfield"
      lead_record_field_stop_token;
  ]

let replace_type_comment_marker_as_lead ?(stop_token = lead_list_stop_token) source marker ~replacement =
  find_lead_marker_target source marker ~stop_token
  |> Option.map (fun (marker_start, marker_end, introducer_offset, style, _) ->
      let text =
        match style with
        | `Own_line ->
            let already_newline =
              introducer_offset < String.length source
              && Char.equal source.[introducer_offset] '\n'
            in
            "\n" ^ replacement ^ if already_newline then "" else "\n"
        | `Inline -> replacement ^ " "
      in
      apply_edits source
        [
          (marker_start, marker_end, "");
          (introducer_offset, introducer_offset, text);
        ])

let find_lead_field_type_marker_target source marker =
  let open Mlx_ast.Parser in
  Option.bind (around_marker source marker)
    (fun (marker_start, marker_end, before, _) ->
      scan_back_unnested
        (function
          | (COLON, _, _) :: (LIDENT _, label_start, _) :: _ ->
              Some (marker_start, marker_end, label_start)
          | _ -> None)
        before)

let replace_field_type_comment_marker_as_lead source marker ~replacement =
  find_lead_field_type_marker_target source marker
  |> Option.map (fun (marker_start, marker_end, label_start) ->
      apply_edits source
        [
          (marker_start, marker_end, "");
          (label_start, label_start, replacement ^ " ");
        ])

let restore_documentation_comment source (comment : documentation_comment) =
  let replacement =
    if comment.is_documentation then print_documentation_comment comment.text
    else print_comment_text comment.text
  in
  let replace = replace_marker_attribute in
  let required message = function
    | Some source -> source
    | None -> failwith (message ^ comment.marker)
  in
  let prefix_message = "missing prefix documentation comment marker " in
  match comment.placement with
  | Record_field ->
    required "missing documentation comment marker "
      (replace source comment.marker ~replacement)
  | Leading_only ->
    let source =
      Option.value (replace source comment.marker ~replacement:"") ~default:source
    in
    required prefix_message
      (replace ~opening:Mlx_ast.Parser.LBRACKETATATAT source comment.marker
         ~replacement:("\n" ^ replacement))
  | Blank_after ->
    let remove opening source =
      Option.value (replace ~opening source comment.marker ~replacement:"") ~default:source
    in
    let source = remove Mlx_ast.Parser.LBRACKETAT (remove Mlx_ast.Parser.LBRACKETATAT source) in
    required prefix_message
      (replace ~opening:Mlx_ast.Parser.LBRACKETATATAT source comment.marker
         ~replacement:("\n" ^ replacement ^ "\n"))
  | Prefix -> (
    match replace source comment.marker ~replacement with
    | Some source ->
        required prefix_message
          (replace ~opening:Mlx_ast.Parser.LBRACKETATATAT source comment.marker
             ~replacement:"")
    | None ->
        let source =
          required prefix_message
            (replace ~opening:Mlx_ast.Parser.LBRACKETATATAT source
               comment.marker ~replacement:("\n" ^ replacement))
        in
        (* A floating comment with nothing to document has no second,
           in-place occurrence to blank. *)
        Option.value
          (replace ~opening:Mlx_ast.Parser.LBRACKETATAT source comment.marker
             ~replacement:"")
          ~default:source)

(* The printer writes a binding as `let f x : t = e` only when neither the
   name nor the function carries an attribute. Otherwise it writes
   `fun x : t -> e`, and a return type that is not atomic needs parens there.
   A comment marker on the function would force that form, so it moves to
   the body. *)
let return_type_parens_marker = "reason_to_mlx.return_type_parens"

let with_return_type_parens (type_ : Ppxlib.Parsetree.core_type) =
  match type_.ptyp_desc with
  | Ptyp_arrow _ | Ptyp_tuple _ | Ptyp_alias _ | Ptyp_poly _ ->
      {
        type_ with
        ptyp_attributes =
          type_.ptyp_attributes
          @ [
               Ppxlib.Ast_helper.Attr.mk ~loc:type_.ptyp_loc
                 { txt = return_type_parens_marker; loc = type_.ptyp_loc }
                 (PStr []);
             ];
      }
  | _ -> type_

let rec parenthesize_return_types (expression : Ppxlib.Parsetree.expression) =
  match expression.pexp_desc with
  | Pexp_newtype (name, inner) ->
      { expression with pexp_desc = Pexp_newtype (name, parenthesize_return_types inner) }
  | Pexp_function (params, constraint_, Pfunction_body inner) ->
      let constraint_ =
        Option.map
          (function
            | Ppxlib.Parsetree.Pconstraint type_ ->
                Ppxlib.Parsetree.Pconstraint (with_return_type_parens type_)
            | Pcoerce _ as coercion -> coercion)
          constraint_
      in
      {
        expression with
        pexp_desc =
          Pexp_function
            (params, constraint_, Pfunction_body (parenthesize_return_types inner));
      }
  | _ -> expression

let rec with_innermost_body_attributes attributes
    (expression : Ppxlib.Parsetree.expression) =
  match expression.pexp_desc with
  | Pexp_newtype (name, inner) ->
      {
        expression with
        pexp_desc = Pexp_newtype (name, with_innermost_body_attributes attributes inner);
      }
  | Pexp_function (_ :: _ as params, constraint_, Pfunction_body inner) ->
      {
        expression with
        pexp_desc =
          Pexp_function
            ( params,
              constraint_,
              Pfunction_body (with_innermost_body_attributes attributes inner) );
      }
  | _ ->
      { expression with pexp_attributes = expression.pexp_attributes @ attributes }

let prepare_function_bindings =
  let is_comment_marker (attribute : Ppxlib.Parsetree.attribute) =
    String.starts_with ~prefix:"reason_to_mlx.comment_" attribute.attr_name.txt
  in
  object
    inherit Ppxlib.Ast_traverse.map as super

    method! value_binding binding =
      let binding = super#value_binding binding in
      match binding.pvb_expr.pexp_desc with
      | Pexp_function (_ :: _, _, _) | Pexp_newtype _ ->
          let markers, kept =
            List.partition is_comment_marker binding.pvb_expr.pexp_attributes
          in
          let expression = { binding.pvb_expr with pexp_attributes = kept } in
          let expression =
            if binding.pvb_pat.ppat_attributes = [] && kept = [] then expression
            else parenthesize_return_types expression
          in
          { binding with pvb_expr = with_innermost_body_attributes markers expression }
      | _ -> binding
  end

let print_bridge_ast ast =
  let buffer = Buffer.create 128 in
  let formatter = Format.formatter_of_buffer buffer in
  (match ast with
  | Implementation ast ->
      Reason.Reason_toolchain.ML.print_implementation_with_comments formatter
        (ast, [])
  | Interface ast ->
      Reason.Reason_toolchain.ML.print_interface_with_comments formatter
        (ast, []));
  Format.pp_print_flush formatter ();
  Buffer.contents buffer

let rec usable_ignore_annotation (type_ : Ppxlib.Parsetree.core_type) =
  match type_.ptyp_desc with
  | Ptyp_any | Ptyp_var _ | Ptyp_arrow _ -> false
  | Ptyp_constr ({ txt = Lident "unit"; _ }, []) -> false
  | Ptyp_poly ([], inner) -> usable_ignore_annotation inner
  | _ -> true

let pattern_annotations pattern =
  let found = ref [] in
  let collector =
    object
      inherit Ppxlib.Ast_traverse.iter as super

      method! pattern pattern =
        match pattern.ppat_desc with
        | Ppat_var name -> found := (name.txt, None) :: !found
        | Ppat_constraint ({ ppat_desc = Ppat_var name; _ }, type_) ->
            found := (name.txt, Some type_) :: !found
        | Ppat_alias (_, name) ->
            found := (name.txt, None) :: !found;
            super#pattern pattern
        | _ -> super#pattern pattern
    end
  in
  collector#pattern pattern;
  !found

let value_binding_annotations (binding : Ppxlib.Parsetree.value_binding) =
  match (binding.pvb_pat.ppat_desc, binding.pvb_constraint) with
  | Ppat_var name, Some (Pvc_constraint { typ; _ }) -> [ (name.txt, Some typ) ]
  | _ -> pattern_annotations binding.pvb_pat

let without_locations =
  object
    inherit Ppxlib.Ast_traverse.map
    method! location _ = Location.none
  end

let annotate_ignore_arguments =
  let annotate annotations (argument : Ppxlib.Parsetree.expression) =
    match argument with
    | {
     pexp_desc = Pexp_ident { txt = Lident name; _ };
     pexp_attributes = [];
     _;
    } -> (
        match List.assoc_opt name annotations with
        | Some (Some type_) when usable_ignore_annotation type_ ->
            let type_ =
              match type_.ptyp_desc with
              | Ptyp_poly ([], inner) -> inner
              | _ -> type_
            in
            Some
              (Ppxlib.Ast_helper.Exp.constraint_ ~loc:argument.pexp_loc argument
                 (without_locations#core_type type_))
        | _ -> None)
    | _ -> None
  in
  object (self)
    inherit [(string * Ppxlib.Parsetree.core_type option) list] Ppxlib.Ast_traverse.map_with_context as super

    method! case annotations case =
      super#case (pattern_annotations case.pc_lhs @ annotations) case

    method! expression annotations expression =
      let expression =
        match expression.pexp_desc with
        | Pexp_function (params, constraint_, body) ->
            let inner =
              List.fold_left
                (fun inner (param : Ppxlib.Parsetree.function_param) ->
                  match param.pparam_desc with
                  | Pparam_val (_, _, pattern) ->
                      pattern_annotations pattern @ inner
                  | Pparam_newtype _ -> inner)
                annotations params
            in
            {
              expression with
              pexp_desc =
                Pexp_function
                  ( List.map (self#function_param annotations) params,
                    Option.map (self#type_constraint annotations) constraint_,
                    self#function_body inner body );
            }
        | Pexp_let (rec_flag, bindings, body) ->
            let inner =
              List.concat_map value_binding_annotations bindings @ annotations
            in
            let binding_annotations =
              match rec_flag with Recursive -> inner | Nonrecursive -> annotations
            in
            {
              expression with
              pexp_desc =
                Pexp_let
                  ( rec_flag,
                    List.map (self#value_binding binding_annotations) bindings,
                    self#expression inner body );
            }
        | Pexp_for (pattern, start, finish, direction, body) ->
            let inner = pattern_annotations pattern @ annotations in
            {
              expression with
              pexp_desc =
                Pexp_for
                  ( pattern,
                    self#expression annotations start,
                    self#expression annotations finish,
                    direction,
                    self#expression inner body );
            }
        | Pexp_letop { let_; ands; body } ->
            let inner =
              List.concat_map
                (fun (binding : Ppxlib.Parsetree.binding_op) ->
                  pattern_annotations binding.pbop_pat)
                (let_ :: ands)
              @ annotations
            in
            {
              expression with
              pexp_desc =
                Pexp_letop
                  {
                    let_ = self#binding_op annotations let_;
                    ands = List.map (self#binding_op annotations) ands;
                    body = self#expression inner body;
                  };
            }
        | _ -> super#expression annotations expression
      in
      let ignored =
        match expression.pexp_desc with
        | Pexp_apply
            ( ({ pexp_desc = Pexp_ident { txt = Lident "ignore"; _ }; _ } as
               callee),
              [ (Nolabel, argument) ] )
        | Pexp_apply
            ( { pexp_desc = Pexp_ident { txt = Lident "|."; _ }; _ },
              [
                (Nolabel, argument);
                ( Nolabel,
                  ({ pexp_desc = Pexp_ident { txt = Lident "ignore"; _ }; _ } as
                   callee) );
              ] ) ->
            Some (callee, argument)
        | _ -> None
      in
      match ignored with
      | Some (callee, argument) ->
          Option.fold ~none:expression
            ~some:(fun argument ->
              {
                expression with
                pexp_desc = Pexp_apply (callee, [ (Nolabel, argument) ]);
              })
            (annotate annotations argument)
      | None -> expression
  end

let split_operator_prefixes = [ "<><"; "<>..."; "</><"; "</>..."; ">..." ]

let reject_split_operators ~input_name =
  let check (loc : Ppxlib.location) name =
    List.iter
      (fun prefix ->
        if String.starts_with ~prefix name then
          failwith
            (Printf.sprintf "%s:%d: operator `%s` is split by the mlx 0.12 lexer"
               input_name loc.loc_start.pos_lnum name))
      split_operator_prefixes
  in
  object
    inherit Ppxlib.Ast_traverse.iter as super

    method! expression expression =
      (match expression.pexp_desc with
      | Pexp_ident { txt; loc } -> check loc (Ppxlib.Longident.last_exn txt)
      | _ -> ());
      super#expression expression

    method! pattern pattern =
      (match pattern.ppat_desc with
      | Ppat_var { txt; loc } -> check loc txt
      | _ -> ());
      super#pattern pattern

    method! value_description description =
      check description.pval_name.loc description.pval_name.txt;
      super#value_description description
  end

let reject_crlf_quoted_strings ~input_name =
  let check (loc : Ppxlib.location) = function
    | Ppxlib.Pconst_string (contents, _, Some _) when contains_crlf contents ->
        failwith
          (Printf.sprintf
             "%s:%d: quoted string holds a CRLF line break, which the OCaml \
              lexer reads as LF"
             input_name loc.loc_start.pos_lnum)
    | _ -> ()
  in
  object
    inherit Ppxlib.Ast_traverse.iter as super

    method! expression expression =
      (match expression.pexp_desc with
      | Pexp_constant constant -> check expression.pexp_loc constant
      | _ -> ());
      super#expression expression

    method! pattern pattern =
      (match pattern.ppat_desc with
      | Ppat_constant constant -> check pattern.ppat_loc constant
      | _ -> ());
      super#pattern pattern
  end

let reject_unspellable_object_fields ~input_name =
  object
    inherit Ppxlib.Ast_traverse.iter as super

    method! object_field field =
      (match field.pof_desc with
      | Otag ({ txt; loc }, _) when not (is_valid_identifier_shape txt) ->
          failwith
            (Printf.sprintf
               "%s:%d: object type field \"%s\" has no OCaml spelling"
               input_name loc.loc_start.pos_lnum txt)
      | Otag _ | Oinherit _ -> ());
      super#object_field field
  end

let print_ocaml_bridge ~kind ~input_name source =
  let lexbuf = Lexing.from_string source in
  Lexing.set_filename lexbuf input_name;
  Location.input_name := input_name;
  Reason.Reason_config.configure ~recoverable:false;
  let lexer = Reason.Reason_toolchain_reason.Lexer.init lexbuf in
  let ast, invalid_docstrings =
    match kind with
    | Structure ->
        let ast, invalid_docstrings =
          Reason.Reason_toolchain_reason.implementation lexer
        in
        (Implementation ast, invalid_docstrings)
    | Signature ->
        let ast, invalid_docstrings =
          Reason.Reason_toolchain_reason.interface lexer
        in
        (Interface ast, invalid_docstrings)
  in
  iter_source (reject_split_operators ~input_name) ast;
  iter_source (reject_crlf_quoted_strings ~input_name) ast;
  iter_source (reject_unspellable_object_fields ~input_name) ast;
  let comments =
    Reason.Reason_toolchain_reason.Lexer.get_comments lexer invalid_docstrings
    |> List.mapi (source_comment source)
    |> merge_split_quote_comments source
  in
  let all_comments = comments in
  let blank_item_mapper = mark_blank_item_lines all_comments in
  let ast = map_source blank_item_mapper ast in
  let ast = map_source preserve_multiline_string_syntax ast in
  let raw_string_mapper = preserve_raw_string_literals () in
  let ast = map_source raw_string_mapper ast in
  let ast =
    map_source
      (object
         method structure = annotate_ignore_arguments#structure []
         method signature = annotate_ignore_arguments#signature []
      end)
      ast
  in
  let scope = collect_intl_scope ast in
  let ast = map_source (normalize_reason_bridge ~input_name ~scope) ast in
  let ast = map_source escape_keyword_identifiers ast in
  let documentation_mapper = preserve_documentation_comments ~text:source ~comments in
  let ast = map_source documentation_mapper ast in
  (* A doc comment stripped from inside an expression has no marker left
     in the tree to restore later, so it's folded into the ordinary
     comment list with a fresh id. *)
  let expression_documentation_comments =
    List.mapi
      (fun i (text, location) -> { id = List.length comments + i; text; location })
      documentation_mapper#expression_documentation
  in
  let comments = comments @ expression_documentation_comments in
  (* marker_comments below must also recognize these: they never went
     through the lexer, so the original all_comments does not have them. *)
  let all_comments = all_comments @ expression_documentation_comments in
  let ast, comments = preserve_declaration_comments ~text:source ast comments in
  let ast, comments = preserve_item_comments ~text:source ~within_items:false ast comments in
  let ast, comments, lead_comments =
    preserve_leading_comments ~text:source ast comments
  in
  let ast, comments, inline_ids = assign_nested_comments ~text:source ast comments in
  let ast, comments = preserve_item_comments ~text:source ~within_items:true ast comments in
  if comments <> [] then failwith "unassigned source comments";
  let ast = map_source prepare_function_bindings ast in
  let blank_expr_mapper = mark_blank_expr_lines all_comments in
  let ast = map_source blank_expr_mapper ast in
  let source = print_bridge_ast ast in
  let source =
    scrub_blank_markers source ~item_marker_count:blank_item_mapper#marker_count
      ~expr_marker_count:blank_expr_mapper#marker_count
  in
  let source =
    List.fold_left restore_raw_string_literal source raw_string_mapper#literals
  in
  let source =
    List.fold_left restore_documentation_comment source
      documentation_mapper#documentation_comments
  in
  let lead_ids = List.map (fun (c : source_comment) -> c.id) lead_comments in
  let marker_comments =
    List.filter
      (fun (c : source_comment) -> not (List.mem c.id lead_ids || List.mem c.id inline_ids))
      all_comments
  in
  let inline_comments =
    List.filter (fun (c : source_comment) -> List.mem c.id inline_ids) all_comments
  in
  (source, marker_comments, lead_comments, inline_comments)

(* The printer puts `;;` before a top-level expression after the floating
   comment markers that precede it, so the comments would end up above the
   `;;` and away from their call. *)
let hoist_toplevel_semisemi source =
  let open Mlx_ast.Parser in
  let rec collect edits run_start tokens =
    match marker_at ~opening:LBRACKETATATAT tokens with
    | Some (name, start_offset, _, rest)
      when String.starts_with ~prefix:"reason_to_mlx.comment_" name ->
        collect edits (Some (Option.value run_start ~default:start_offset)) rest
    | _ ->
    match tokens with
    | [] -> edits
    | (SEMISEMI, start_offset, end_offset) :: rest ->
        let edits =
          match run_start with
          | Some marker_start ->
              (marker_start, marker_start, ";;\n") :: (start_offset, end_offset, "") :: edits
          | None -> edits
        in
        collect edits None rest
    | _ :: rest -> collect edits None rest
  in
  apply_edits source (collect [] None (lex_tokens source))

let remove_return_type_parens_markers source =
  let open Mlx_ast.Parser in
  let rec collect edits tokens =
    match marker_at ~opening:LBRACKETAT tokens with
    | Some (name, start_offset, end_offset, rest)
      when String.equal name return_type_parens_marker ->
        collect ((start_offset, end_offset, "") :: edits) rest
    | _ -> ( match tokens with _ :: rest -> collect edits rest | [] -> edits)
  in
  apply_edits source (collect [] (lex_tokens source))

let comment_failure ~input_name (comment : source_comment) message =
  failwith
    (Printf.sprintf "%s:%d: %s (comment: %s)" input_name
       comment.location.loc_start.pos_lnum message
       (String.trim comment.text))

let replace_comment_markers ~input_name source comments =
  let source = hoist_toplevel_semisemi source in
  let source = remove_return_type_parens_markers source in
  List.fold_left
    (fun source (comment : source_comment) ->
      let replacement = print_comment_text comment.text in
      let name = marker_name "comment" comment in
      List.find_map
        (fun replace -> replace source)
        [
          (fun source ->
            replace_node_comment_marker_as_lead ~inside:false ~constructor:false source
              (marker_name "leadnodecomment" comment)
              ~replacement);
          (fun source ->
            replace_node_comment_marker_as_lead ~inside:false ~constructor:true source
              (marker_name "leadpatterncomment" comment)
              ~replacement);
          (fun source ->
            replace_node_comment_marker_as_lead ~inside:true ~constructor:false source
              (marker_name "leadchildcomment" comment)
              ~replacement);
          (fun source ->
            replace_type_comment_marker_as_lead ~stop_token:lead_stop_token source
              (marker_name "leadaltcomment" comment)
              ~replacement);
          (fun source ->
            replace_field_type_comment_marker_as_lead source
              (marker_name "leadfieldcomment" comment)
              ~replacement);
          (fun source ->
            replace_type_comment_marker_as_lead source
              (marker_name "leadtypecomment" comment)
              ~replacement);
          (fun source ->
            replace_type_comment_marker source
              (marker_name "typecomment" comment)
              ~replacement);
          (fun source ->
            replace_trailing_marker_attribute source
              (marker_name "trailingcomment" comment)
              ~replacement);
          (fun source -> replace_marker_attribute source name ~replacement);
          (fun source ->
            replace_marker_attribute ~opening:Mlx_ast.Parser.LBRACKETATAT
              source name ~replacement);
          (fun source ->
            replace_marker_attribute ~opening:Mlx_ast.Parser.LBRACKETATATAT
              source name ~replacement);
        ]
      |> function
      | Some source -> source
      | None ->
          comment_failure ~input_name comment
            "the Reason printer dropped the marker that carries this comment")
    source comments

let adjacent_marker_runs tokens =
  let open Mlx_ast.Parser in
  let close runs current = if current = [] then runs else current :: runs in
  let rec go runs current tokens =
    match marker_at ~opening:LBRACKETAT tokens with
    | Some (name, _, _, rest) -> go runs (name :: current) rest
    | None -> (
        match tokens with
        | _ :: rest -> go (close runs current) [] rest
        | [] -> close runs current)
  in
  go [] [] tokens

(* The formatter fills a comment before a labelled argument onto the previous
   line when it breaks there, where it reads as that argument's. Placed after
   the label it stays with its own argument, together with the comments that
   lead the same argument, so they keep their order. *)
let trailing_arg_leads ~marked ~formatted comments =
  let marked_tokens = lex_tokens marked in
  let is_own_line_arg comment =
    Option.is_some (find_marker marked_tokens (marker_name "leadargown" comment))
  in
  let rec ends_a_code_line text from =
    match String.find_first ~sub:text ~start:from formatted with
    | None -> false
    | Some start ->
        let stop = start + String.length text in
        let line_start =
          match String.rindex_from_opt formatted start '\n' with
          | Some i -> i + 1
          | None -> 0
        in
        let line_end =
          Option.value
            (String.index_from_opt formatted stop '\n')
            ~default:(String.length formatted)
        in
        let blank part = String.trim part = "" in
        ((not (blank (String.sub formatted line_start (start - line_start))))
        && blank (String.sub formatted stop (line_end - stop)))
        || ends_a_code_line text stop
  in
  let ends_a_code_line_comment (comment : source_comment) =
    is_own_line_arg comment
    && ends_a_code_line (print_comment_text comment.text) 0
  in
  let runs = adjacent_marker_runs marked_tokens in
  let leads_same_argument (comment : source_comment) (other : source_comment) =
    List.exists
      (fun run ->
        List.mem (marker_name "leadargown" comment) run
        && List.mem (marker_name "leadargown" other) run)
      runs
  in
  let line_enders = List.filter ends_a_code_line_comment comments in
  List.filter
    (fun comment -> List.exists (leads_same_argument comment) line_enders)
    comments

let own_line_args_to_values marked comments =
  let tokens = lex_tokens marked in
  apply_edits marked
    (List.filter_map
       (fun comment ->
         find_marker tokens (marker_name "leadargown" comment)
         |> Option.map (fun (start_offset, end_offset) ->
             ( start_offset,
               end_offset,
               "[@" ^ marker_name "leadvalue" comment ^ "]" )))
       comments)

let skip_blank_lines source offset =
  let len = String.length source in
  let rec go i last_newline =
    if i < len && Char.equal source.[i] '\n' then go (i + 1) (Some (i + 1))
    else if i < len && Char.Ascii.is_white source.[i] then go (i + 1) last_newline
    else match last_newline with Some pos -> pos | None -> offset
  in
  go offset None

(* A comment before a case, an `and` or the first let after an opening
   paren needs the empty line this leaves, or ocamlformat-mlx reads it as
   trailing; a let-chain link keeps the line, so it gets none. *)
let is_let_chain_link source offset =
  let last = blank_start source offset - 1 in
  offset + 3 <= String.length source
  && String.equal (String.sub source offset 3) "let"
  && last >= 2
  && source.[last] = 'n'
  && source.[last - 1] = 'i'
  && not (Char.Ascii.is_alphanum source.[last - 2] || source.[last - 2] = '_')
  && String.contains (String.sub source (last + 1) (offset - last - 1)) '\n'

(* The Reason printer writes `let f = fun x -> e` for a binding whose name
   carries an attribute, where it writes `let f x = e` otherwise. Once the
   marker is gone the sugar is restored, so a comment costs no layout. *)
let function_sugar_edits source ids =
  let open Mlx_ast.Parser in
  let rec markers tokens =
    match marker_at ~opening:LBRACKETAT tokens with
    | Some (name, _, _, rest)
      when Option.fold ~none:false
             ~some:(fun id -> List.mem id ids)
             (marker_id ~prefix:"reason_to_mlx.lead_" name) ->
        markers rest
    | _ -> tokens
  in
  let rec arrow depth = function
    | [] -> None
    | ( ( LPAREN | LBRACKET | LBRACE | LBRACKETAT | LBRACKETATAT
        | LBRACKETATATAT | LBRACKETPERCENT | LBRACKETPERCENTPERCENT ),
        _,
        _ )
      :: rest ->
        arrow (depth + 1) rest
    | ((RPAREN | RBRACKET | RBRACE), _, _) :: rest -> arrow (depth - 1) rest
    | (MINUSGREATER, start_offset, end_offset) :: rest when depth = 0 ->
        Some ((start_offset, end_offset), rest)
    | _ :: rest -> arrow depth rest
  in
  let delete (_, start_offset, end_offset) = (start_offset, end_offset, "") in
  let is_newtype_binder = function
    | [] -> false
    | tokens ->
        List.for_all
          (function
            | (LPAREN | TYPE | RPAREN | LIDENT _), _, _ -> true
            | _ -> false)
          tokens
  in
  let rec sugar params =
    Option.bind (arrow 0 params) (fun ((arrow_start, arrow_end), after) ->
        let binder =
          List.filter (fun (_, offset, _) -> offset < arrow_start) params
        in
        match after with
        | ((FUN, _, _) as fun_) :: next when is_newtype_binder binder ->
            Option.map
              (fun edits ->
                (arrow_start, arrow_end, "") :: delete fun_ :: edits)
              (sugar next)
        | _ -> Some [ (arrow_start, arrow_end, "=") ])
  in
  let rec go edits = function
    | [] -> edits
    | ((LPAREN, _, _) as outer_open) :: ((LPAREN, _, _) as inner_open)
      :: (LIDENT _, _, _) :: ((RPAREN, _, _) as inner_close) :: rest
      when markers rest != rest -> (
        match markers rest with
        | ((RPAREN, _, _) as outer_close) :: ((EQUAL, _, _) as equal)
          :: ((FUN, _, _) as fun_) :: params -> (
            match sugar params with
            | Some arrow_edits ->
                go
                  (arrow_edits
                  @ List.map delete
                      [ outer_open; inner_open; inner_close; outer_close; equal; fun_ ]
                  @ edits)
                  params
            | None -> go edits rest)
        | _ -> go edits rest)
    | _ :: rest -> go edits rest
  in
  go [] (lex_tokens source)

let restore_leading_comments ~input_name source comments =
  let find_target comment =
    match
      List.find_map
        (fun (kind, find) -> find source (marker_name kind comment))
        lead_marker_kinds
    with
    | Some target -> target
    | None ->
        comment_failure ~input_name comment
          "the Reason printer dropped the marker that carries this comment"
  in
  let targets =
    List.map (fun (comment : source_comment) -> (comment, find_target comment)) comments
  in
  let offset_of (_, (_, _, offset, _, _)) = offset in
  let inserts =
    List.sort_uniq compare (List.map offset_of targets)
    |> List.map (fun offset ->
        let members =
          List.filter (fun target -> offset_of target = offset) targets
          |> List.sort (fun ((a : source_comment), _) (b, _) ->
              compare a.id b.id)
        in
        let style =
          match members with
          | (_, (_, _, _, style, _)) :: _ -> style
          | [] -> `Own_line
        in
        let texts =
          List.map
            (fun ((comment : source_comment), _) ->
              print_comment_text comment.text)
            members
        in
        match style with
        | `Own_line ->
            let content_offset = skip_blank_lines source offset in
            if content_offset = offset then
              (* Skip a second newline, or it reads as trailing. *)
              let already_newline =
                offset < String.length source
                && Char.equal source.[offset] '\n'
              in
              ( offset,
                offset,
                (if is_let_chain_link source offset then "" else "\n")
                ^ String.concat "\n" texts
                ^ if already_newline then "" else "\n" )
            else
              (content_offset, content_offset, String.concat "\n" texts ^ "\n")
        | `Inline -> (offset, offset, String.concat " " texts ^ " "))
  in
  let deletes =
    List.concat_map
      (fun (_, (marker_start, marker_end, _, _, extra_deletes)) ->
        (marker_start, marker_end, "")
        :: List.map (fun (start_, end_) -> (start_, end_, "")) extra_deletes)
      targets
  in
  let ids = List.map (fun (c : source_comment) -> c.id) comments in
  apply_edits source (inserts @ deletes @ function_sugar_edits source ids)

let is_reason_only_attribute (attribute : Mlx_ast.Parsetree.attribute) =
  is_reason_only_attribute_name attribute.attr_name.txt

let is_react_component_attribute (attribute : Mlx_ast.Parsetree.attribute) =
  is_react_component_attribute_name attribute.attr_name.txt

let is_mlx_jsx_attribute (attribute : Mlx_ast.Parsetree.attribute) =
  String.equal attribute.attr_name.txt "JSX"

let find_jsx_attribute (attributes : Mlx_ast.Parsetree.attribute list) =
  match List.partition is_mlx_jsx_attribute attributes with
  | [ jsx_attribute ], other_attributes -> Some (jsx_attribute, other_attributes)
  | _ -> None

let normalize_reason_ast ~associative_operators =
  let default = Mlx_ast.Ast_mapper.default_mapper in
  let only_unlabelled arguments =
    List.for_all
      (fun ((label : Mlx_ast.Asttypes.arg_label), _) -> label = Mlx_ast.Asttypes.Nolabel)
      arguments
  in
  let rec associative_operator_operands operator_name expression operands =
    match expression.Mlx_ast.Parsetree.pexp_desc with
    | Pexp_infix ({ txt; _ }, left, right)
      when String.equal txt operator_name ->
        associative_operator_operands operator_name left
          (associative_operator_operands operator_name right operands)
    | _ -> expression :: operands
  in
  let rec pipe_chain (expression : Mlx_ast.Parsetree.expression) =
    match expression.pexp_desc with
    | Pexp_apply (callee, _) ->
        let count, expressions = pipe_chain callee in
        if count = 0 then (0, []) else (count, expression :: expressions)
    | Pexp_infix ({ txt = "|."; _ }, argument, _) ->
        let count, expressions = pipe_chain argument in
        (count + 1, expression :: expressions)
    | _ -> (0, [])
  in
  let preserved_pipe_expressions = ref [] in
  let attributes mapper attributes =
    attributes
    |> List.filter (fun attribute -> not (is_reason_only_attribute attribute))
    |> List.map (mapper.Mlx_ast.Ast_mapper.attribute mapper)
  in
  let add_binding_extension ?(documentation = []) extension bindings =
    let pvbs_bindings =
      match bindings.Mlx_ast.Parsetree.pvbs_bindings with
      | [] -> []
      | binding :: bindings ->
          let attributes = binding.pvb_attributes in
          (* ocamlformat's warning 50 accepts `let%ext[@ocaml.doc ...]
             name` but rejects the same move on a plain `let`. *)
          let doc_comment, attrs_after =
            List.partition
              (fun (attribute : Mlx_ast.Parsetree.attribute) ->
                String.equal attribute.attr_name.txt "ocaml.doc")
              attributes.attrs_after
          in
          let pvb_attributes =
            {
              Mlx_ast.Parsetree.attrs_extension = Some extension;
              attrs_before = attributes.attrs_before @ doc_comment;
              attrs_after = attrs_after @ documentation;
            }
          in
          { binding with pvb_attributes } :: bindings
    in
    { bindings with pvbs_bindings }
  in
  let structure_item mapper item =
    let item = default.structure_item mapper item in
    match item.pstr_desc with
    | Pstr_extension
        ( ( ({ txt = "melange_only"; _ } as extension),
            PStr
              [ { pstr_desc = Pstr_value bindings; _ } ] ),
          documentation )
      when List.for_all
             (fun (attribute : Mlx_ast.Parsetree.attribute) ->
               String.equal attribute.attr_name.txt "ocaml.doc")
             documentation ->
        {
          item with
          pstr_desc =
            Pstr_value
              (add_binding_extension ~documentation extension bindings);
        }
    | _ -> item
  in
  let value_binding mapper binding =
    let binding = default.value_binding mapper binding in
    let attributes = binding.pvb_attributes in
    (* The OCaml bridge loses the prefix position used by Reason components. *)
    let react_component, attrs_after =
      List.partition is_react_component_attribute attributes.attrs_after
    in
    let pvb_attributes =
      {
        attributes with
        attrs_before = attributes.attrs_before @ react_component;
        attrs_after;
      }
    in
    { binding with pvb_attributes }
  in
  let expr mapper expression =
    let previous_preserved_pipe_expressions = !preserved_pipe_expressions in
    let count, pipe_expressions = pipe_chain expression in
    (* [(f x) ~l] erases optionals before [x]; [x |. f ~l] does not. *)
    let single_stage_has_label =
      count = 1
      &&
      match expression.Mlx_ast.Parsetree.pexp_desc with
      | Pexp_apply (_, args) ->
          expression.pexp_attributes = [] && not (only_unlabelled args)
      | _ -> false
    in
    if count > 1 || single_stage_has_label then
      preserved_pipe_expressions :=
        pipe_expressions @ previous_preserved_pipe_expressions;
    let preserve_pipe_call = List.memq expression !preserved_pipe_expressions in
    let expression =
      Fun.protect
        ~finally:(fun () ->
          preserved_pipe_expressions := previous_preserved_pipe_expressions)
        (fun () -> default.expr mapper expression)
    in
    let fragment children attrs =
      let loc = Ocamlformat_ocaml_common.Location.none in
      let located txt = { Ocamlformat_ocaml_common.Location.txt; loc } in
      let callee =
        Mlx_ast.Ast_helper.Exp.ident ~loc
          (located (Ocamlformat_ocaml_common.Longident.Lident ""))
      in
      let children_loc =
        let open Ocamlformat_ocaml_common.Location in
        let open Lexing in
        match (children, List.rev children) with
        | first :: _, last :: _ ->
            {
              expression.pexp_loc with
              loc_start = first.Mlx_ast.Parsetree.pexp_loc.loc_start;
              loc_end = last.Mlx_ast.Parsetree.pexp_loc.loc_end;
            }
        | _ ->
            let opening_end =
              {
                expression.pexp_loc.loc_start with
                pos_cnum = expression.pexp_loc.loc_start.pos_cnum + 2;
              }
            in
            {
              expression.pexp_loc with
              loc_start = opening_end;
              loc_end = opening_end;
            }
      in
      let children =
        {
          expression with
          pexp_loc = children_loc;
          pexp_desc = Pexp_list children;
          pexp_attributes = [];
        }
      in
      let unit =
        Mlx_ast.Ast_helper.Exp.construct ~loc
          (located (Ocamlformat_ocaml_common.Longident.Lident "()"))
          None
      in
      Mlx_ast.Ast_helper.Exp.apply ~loc:expression.pexp_loc ~attrs callee
        [
          (Mlx_ast.Asttypes.Nolabel, unit);
          (Mlx_ast.Asttypes.Labelled (located "children"), children);
        ]
    in
    match expression with
    | {
     pexp_desc =
       Pexp_extension
         ( ({ txt = "melange_only"; _ } as extension),
           PStr
             [
               {
                 pstr_desc =
                   Pstr_eval
                     ( {
                         pexp_desc =
                           Pexp_let (bindings, body, in_loc);
                         _;
                       },
                       [] );
                 _;
               };
             ] );
     _;
    } ->
        {
          expression with
          pexp_desc =
            Pexp_let
              (add_binding_extension extension bindings, body, in_loc);
        }
    | {
     pexp_desc =
       Pexp_extension
         ( ({ txt = "platform"; _ } as extension),
           PStr
             [
               {
                 pstr_desc =
                   Pstr_eval
                     ( {
                         pexp_desc =
                           Pexp_match (subject, cases, infix);
                         _;
                       },
                       [] );
                 _;
               };
             ] );
     _;
    } ->
        {
          expression with
          pexp_desc =
            Pexp_match
              (subject, cases, { infix with infix_ext = Some extension });
        }
    | {
     pexp_desc =
       Pexp_infix
         (({ txt = operator_name; _ } as operator), _, _);
     _;
    }
      when List.mem operator_name associative_operators -> (
        match associative_operator_operands operator_name expression [] with
        | first :: rest ->
            let rec chain left = function
              | [] -> left
              | (right : Mlx_ast.Parsetree.expression) :: more ->
                  let pexp_loc =
                    if more = [] then expression.pexp_loc
                    else { expression.pexp_loc with loc_end = right.pexp_loc.loc_end }
                  in
                  chain
                    { expression with
                      pexp_loc;
                      pexp_desc = Pexp_infix (operator, left, right) }
                    more
            in
            chain first rest
        | [] -> expression)
    | {
     pexp_desc =
       Pexp_apply
         ( {
             pexp_desc = Pexp_apply (callee, first_arguments);
             pexp_attributes = [];
             _;
           },
           remaining_arguments );
     pexp_attributes = [];
     _;
    }
      when (not preserve_pipe_call)
           && only_unlabelled first_arguments
           && only_unlabelled remaining_arguments ->
        {
          expression with
          pexp_desc =
            Pexp_apply
              (callee, first_arguments @ remaining_arguments);
        }
    | {
     pexp_desc =
       Pexp_infix
         ( { txt = "|."; _ },
           argument,
           ({ pexp_desc = Pexp_ident _; _ } as callee) );
     _;
    }
      when not preserve_pipe_call ->
        {
          expression with
          pexp_desc =
            Pexp_apply
              (callee, [ (Mlx_ast.Asttypes.Nolabel, argument) ]);
        }
    | {
     pexp_desc =
       Pexp_apply
         ( {
             pexp_desc =
               Pexp_infix
                 ( ({ txt = "|."; _ } as operator),
                   argument,
                   ({ pexp_desc = Pexp_ident _; _ } as callee)
                 );
             _;
           },
           stage_arguments );
     pexp_attributes = [];
     _;
    } ->
        (* Melange turns `(a |. f) args` into `(f a) args` and `a |. f args`
           into `f a args`, which can type a labelled argument before `a`:
           a lambda that reads record fields then fails to typecheck, and
           the build reports it. The synthesized node must not inherit
           callee's own attributes, or they print twice. *)
        {
          expression with
          pexp_desc =
            Pexp_infix
              ( operator,
                argument,
                {
                  callee with
                  pexp_desc =
                    Pexp_apply (callee, stage_arguments);
                  pexp_attributes = [];
                } );
        }
    | { pexp_desc = Pexp_list children; pexp_attributes; _ }
      ->
        if List.exists is_mlx_jsx_attribute pexp_attributes then
          fragment children pexp_attributes
        else expression
    | {
     pexp_desc =
       Pexp_construct
         ({ txt = Ocamlformat_ocaml_common.Longident.Lident "[]"; _ }, None);
     pexp_attributes;
     _;
    } -> (
        match find_jsx_attribute pexp_attributes with
        | Some _ -> fragment [] pexp_attributes
        | None -> expression)
    | {
     pexp_desc = Pexp_apply (callee, arguments);
     pexp_attributes;
     _;
    } ->
        if not (List.exists is_mlx_jsx_attribute pexp_attributes) then
          expression
        else
          let is_children_argument = function
            | Mlx_ast.Asttypes.Labelled { txt = "children"; _ }, _ -> true
            | _ -> false
          in
          let is_empty_children_argument = function
            | ( Mlx_ast.Asttypes.Labelled { txt = "children"; _ },
                {
                  Mlx_ast.Parsetree.pexp_desc =
                    Pexp_construct
                      ( {
                          txt = Ocamlformat_ocaml_common.Longident.Lident "[]";
                          _;
                        },
                        None );
                  _;
                } ) ->
                true
            | _ -> false
          in
          let rec drop_first_empty_children = function
            | [] -> []
            | argument :: rest when is_empty_children_argument argument -> rest
            | argument :: rest -> argument :: drop_first_empty_children rest
          in
          let arguments =
            if List.length (List.filter is_children_argument arguments) > 1 then
              List.rev (drop_first_empty_children (List.rev arguments))
            else arguments
          in
          {
            expression with
            pexp_desc =
              Pexp_apply
                (callee, arguments);
          }
    | expression -> expression
  in
  { default with attributes; expr; structure_item; value_binding }

let render_initial_mlx ~kind ~associative_operators ~input_name ~conf source =
  let render fragment =
    let parsed =
      Mlx.Parse_with_comments.parse
        (Mlx.Parse_with_comments.parse_ast conf)
        fragment conf ~input_name ~source
    in
    let ast =
      Mlx.Extended_ast.map fragment
        (normalize_reason_ast ~associative_operators)
        parsed.ast
    in
    let comments =
      Mlx.Cmts.init fragment ~debug:false parsed.source ast parsed.comments
    in
    let default = Mlx_ast.Ast_mapper.default_mapper in
    (* Relocate only moves a comment after a location, never before. *)
    let leaf_locations (value : Mlx_ast.Parsetree.expression) =
      match value.pexp_desc with
      | Pexp_ident lid -> [ value.pexp_loc; lid.loc ]
      | Pexp_constant constant ->
          [ value.pexp_loc; constant.pconst_loc ]
      | Pexp_construct (lid, None) ->
          [ value.pexp_loc; lid.loc ]
      | _ -> [ value.pexp_loc ]
    in
    let relocate_to_leading src_locations ~leading_anchor =
      List.iter
        (fun src ->
          Mlx.Cmts.relocate comments ~src ~before:leading_anchor
            ~after:leading_anchor)
        src_locations
    in
    let expr mapper expression =
      let expression = default.expr mapper expression in
      (match expression.pexp_desc with
      | Pexp_extension
          (name, PStr [ ({ pstr_desc = Pstr_eval (inner, _); _ } as item) ]) ->
          Mlx.Cmts.relocate comments ~src:name.loc ~before:expression.pexp_loc
            ~after:name.loc;
          List.iter
            (fun src ->
              Mlx.Cmts.relocate comments ~src ~before:src
                ~after:expression.pexp_loc)
            [ item.pstr_loc; inner.pexp_loc ]
      | _ -> ());
      (match find_jsx_attribute expression.Mlx_ast.Parsetree.pexp_attributes with
      | Some ({ attr_name = { loc; _ }; attr_loc; _ }, _other_attributes) ->
          (* JSX attribute comments belong to the element, not the attribute. *)
          List.iter
            (fun src ->
              Mlx.Cmts.relocate comments ~src ~before:expression.pexp_loc
                ~after:expression.pexp_loc)
            [ loc; attr_loc ];
          (* A comment before the first child leads, not tags the JSX. *)
          (match expression.pexp_desc with
          | Pexp_apply (callee, arguments) -> (
              let is_children_label = function
                | Mlx_ast.Asttypes.Labelled { txt = "children"; _ } -> true
                | Mlx_ast.Asttypes.Labelled _ | Mlx_ast.Asttypes.Nolabel | Mlx_ast.Asttypes.Optional _ -> false
              in
              (* The synthesized unit argument is not a real prop. *)
              let is_unit (value : Mlx_ast.Parsetree.expression) =
                match value.pexp_desc with
                | Pexp_construct
                    ( { txt = Ocamlformat_ocaml_common.Longident.Lident "()"; _ },
                      None ) ->
                    true
                | _ -> false
              in
              (* Punning drops the identifier's own location, so a comment
                 attached there is lost; the expression's location is the
                 one the printer checks. *)
              List.iter
                (fun (label, (value : Mlx_ast.Parsetree.expression)) ->
                  match (label, value.pexp_desc) with
                  | ( ( Mlx_ast.Asttypes.Labelled { txt = name; _ }
                      | Mlx_ast.Asttypes.Optional { txt = name; _ } ),
                      Pexp_ident
                        { txt = Ocamlformat_ocaml_common.Longident.Lident ident;
                          loc } )
                    when String.equal name ident ->
                      Mlx.Cmts.relocate comments ~src:loc
                        ~before:value.pexp_loc ~after:value.pexp_loc
                  | _ -> ())
                arguments;
              let last_tag_value =
                List.fold_left
                  (fun last (label, value) ->
                    if is_children_label label || is_unit value then last
                    else Some value)
                  None arguments
              in
              (* A fragment's callee has no location. *)
              let tag_locations =
                match last_tag_value with
                | Some value -> leaf_locations value
                | None ->
                    if
                      callee.pexp_loc = expression.pexp_loc
                      || callee.pexp_loc = Ocamlformat_ocaml_common.Location.none
                    then []
                    else leaf_locations callee
              in
              (* A component's tag_loc is the callee's own node; a DOM
                 tag's is the identifier's inner loc instead. *)
              let is_component_callee =
                match callee.Mlx_ast.Parsetree.pexp_desc with
                | Pexp_ident
                    { txt = Ocamlformat_ocaml_common.Longident.Ldot _; _ } ->
                    true
                | _ -> false
              in
              if callee.pexp_loc <> expression.pexp_loc then
                List.iter
                  (fun src ->
                    Mlx.Cmts.relocate comments ~src ~before:expression.pexp_loc
                      ~after:src)
                  (leaf_locations callee);
              (match callee.pexp_desc with
              | Pexp_ident
                  { txt = Ocamlformat_ocaml_common.Longident.Ldot (prefix, name); _ }
                when callee.pexp_loc <> expression.pexp_loc ->
                  relocate_to_leading
                    (leaf_locations callee @ [ prefix.loc; name.loc ])
                    ~leading_anchor:callee.pexp_loc
              | _ -> ());
              let children =
                List.find_map
                  (fun (label, (value : Mlx_ast.Parsetree.expression)) ->
                    if is_children_label label then
                      match value.pexp_desc with
                      | Pexp_list (_ :: _ as children) ->
                          Some (value, children)
                      | Pexp_list [] | _ -> None
                    else None)
                  arguments
              in
              (match children with
              | Some (list, (first :: _ as children)) ->

                  (* A fragment's list starts where its first child does, so
                     a comment before that child lands on the list. *)
                  Mlx.Cmts.relocate comments ~src:list.pexp_loc
                    ~before:first.pexp_loc ~after:list.pexp_loc;
                  (* A comment leading the first child has nowhere to go but
                     forward: Cmts never moves a comment before a location,
                     so it lands on the tag itself unless relocated. *)
                  let last_child =
                    (List.nth children (List.length children - 1))
                      .Mlx_ast.Parsetree.pexp_loc
                  in
                  List.iter
                    (fun src ->
                      Mlx.Cmts.relocate comments ~src ~before:src
                        ~after:last_child)
                    tag_locations
              | Some (_, []) | None ->
                  if Option.is_none last_tag_value && is_component_callee then
                    (* No prop and no real child leaves nothing else to
                       anchor to; land the comment on the callee's own
                       node, per tag_loc above. *)
                    relocate_to_leading tag_locations
                      ~leading_anchor:callee.pexp_loc))
          | _ -> ())
      | None -> ());
      expression
    in
    let ast = Mlx.Extended_ast.map fragment { default with expr } ast in
    let buffer = Buffer.create (String.length source) in
    let formatter = Ocamlformat_format.Format_.formatter_of_buffer buffer in
    let open Mlx.Fmt in
    let document =
      set_margin conf.fmt_opts.margin.v
      $ set_max_indent conf.fmt_opts.max_indent.v
      $ fmt_if
          (not (String.equal parsed.prefix ""))
          (str parsed.prefix $ force_newline)
      $ Mlx.Fmt_ast.fmt_ast fragment ~debug:false parsed.source comments conf
          ast
    in
    eval formatter document;
    (match Mlx.Cmts.remaining_comments comments with
    | [] -> ()
    | comments ->
        failwith
          ("MLX rendering left comments unprinted: "
          ^ String.concat "; " (List.map Mlx.Cmt.txt comments)));
    Ocamlformat_format.Format_.pp_print_flush formatter ();
    if Buffer.length buffer > 0 then
      Ocamlformat_format.Format_.pp_print_newline formatter ();
    Buffer.contents buffer
  in
  match kind with
  | Structure -> render Mlx.Extended_ast.Structure
  | Signature -> render Mlx.Extended_ast.Signature

let mlx_syntax = function
  | Structure -> Mlx.Syntax.Structure
  | Signature -> Mlx.Syntax.Signature

let format_error error =
  Format.asprintf "%a"
    (Mlx.Translation_unit.Error.print ~debug:false ~quiet:false)
    error

let format_mlx ~kind ~input_name ~conf source =
  let syntax = mlx_syntax kind in
  match
    Mlx.Translation_unit.parse_and_format syntax ~input_name ~source conf
  with
  | Ok source -> source
  | Error error ->
      let message = format_error error in
      if String.includes ~affix:"BUG: comment changed." message then
        source
      else failwith message

(* format_mlx can silently swallow a comment-changed error. *)
(* Normalize whitespace and drop quotes so comments compare equal. *)
let normalize_comment_text text =
  let buffer = Buffer.create (String.length text) in
  let pending_space = ref false in
  String.iter
    (fun c ->
      match c with
      | ' ' | '\t' | '\n' | '\r' -> pending_space := true
      | '"' -> ()
      | c ->
          if !pending_space && Buffer.length buffer > 0 then
            Buffer.add_char buffer ' ';
          pending_space := false;
          Buffer.add_char buffer c)
    text;
  Buffer.contents buffer

(* A silent comment drop would not otherwise fail the build. *)
let check_comments_preserved ~input_name source comments =
  let normalized_source = normalize_comment_text source in
  List.iter
    (fun (comment : source_comment) ->
      (* Compare print_comment_text's output, not raw text. *)
      let normalized_text =
        normalize_comment_text (escape_ocaml_comment comment.text)
      in
      if
        String.length normalized_text > 0
        && Option.is_none (String.find_first ~sub:normalized_text normalized_source)
      then
        failwith
          (Printf.sprintf
             "%s: comment dropped from output (comment id %d): %s" input_name
             comment.id normalized_text))
    comments

let check_format_stable ~kind ~input_name ~conf source =
  let syntax = mlx_syntax kind in
  match Mlx.Translation_unit.parse_and_format syntax ~input_name ~source conf with
  | Ok reformatted when String.equal reformatted source -> ()
  | Ok _ ->
      failwith
        "reason-to-mlx: converter output is not stable under the pinned \
         formatter (reformatting it produces different text) -- refusing to \
         emit output that would fail the project's formatter check"
  | Error error ->
      failwith
        ("reason-to-mlx: converter output does not survive reformatting by \
          the pinned formatter: " ^ format_error error)

(* ocamlformat-mlx alternates between two layouts for some comments before
   a quoted string. *)
let comments_before_quoted_string text comments =
  let length = String.length text in
  let rec opens_quoted_string offset =
    offset < length
    &&
    match text.[offset] with
    | '|' -> true
    | 'a' .. 'z' | '_' -> opens_quoted_string (offset + 1)
    | _ -> false
  in
  List.filter
    (fun (comment : source_comment) ->
      let next = blank_end text comment.location.loc_end.pos_cnum in
      next < length && text.[next] = '{' && opens_quoted_string (next + 1))
    comments

let syntax_failure ~input_name ~comments source error =
  let line =
    (Ocamlformat_ocaml_common.Syntaxerr.location_of_error error).loc_start
      .pos_lnum
  in
  let lines = Array.of_list (String.split_on_char '\n' source) in
  let window =
    String.concat "\n"
      (List.filteri
         (fun index _ -> abs (index + 1 - line) <= 1)
         (Array.to_list lines))
  in
  let nearby =
    List.filter
      (fun (comment : source_comment) ->
        String.includes ~affix:(print_comment_text comment.text) window)
      comments
  in
  let failing_line =
    String.trim
      (if line >= 1 && line <= Array.length lines then lines.(line - 1) else "")
  in
  failwith
    (match nearby with
    | [] ->
        Printf.sprintf
          "%s: the converted text does not parse at line %d of the text \
           after placing comments: %s"
          input_name line failing_line
    | comments ->
        Printf.sprintf
          "%s:%s: the converted text does not parse after placing the \
           comment here (line %d of the text after placing comments: %s)"
          input_name
          (String.concat ","
             (List.map
                (fun (comment : source_comment) ->
                  string_of_int comment.location.loc_start.pos_lnum)
                comments))
          line failing_line)

let shift_continuation_lines delta text =
  match String.split_on_char '\n' text with
  | [] | [ _ ] -> text
  | first :: rest ->
      let shift line =
        if String.trim line = "" then line
        else if delta >= 0 then String.make delta ' ' ^ line
        else
          let spaces =
            Option.value ~default:(String.length line)
              (String.find_first_index (fun char -> char <> ' ') line)
          in
          let drop = min (-delta) spaces in
          String.sub line drop (String.length line - drop)
      in
      String.concat "\n" (first :: List.map shift rest)

let occurrences ~sub text =
  let rec go from acc =
    match String.find_first ~start:from ~sub text with
    | Some found -> go (found + 1) (found :: acc)
    | None -> List.rev acc
  in
  if String.equal sub "" then [] else go 0 []

let realign_comment_continuations source comments =
  List.fold_left
    (fun source (comment : source_comment) ->
      let printed = print_comment_text comment.text in
      if not (String.contains printed '\n') then source
      else
        match occurrences ~sub:printed source with
        | [ offset ] ->
            let line_start =
              match String.rindex_from_opt source (max 0 (offset - 1)) '\n' with
              | Some newline when offset > 0 -> newline + 1
              | Some _ | None -> 0
            in
            let source_column =
              comment.location.loc_start.pos_cnum - comment.location.loc_start.pos_bol
            in
            let delta = offset - line_start - source_column in
            if delta = 0 then source
            else
              apply_edits source
                [
                  ( offset,
                    offset + String.length printed,
                    print_comment_text (shift_continuation_lines delta comment.text) );
                ]
        | _ -> source)
    source comments

let convert_exn ~conf ~associative_operators ~kind ~input_name ~output_name reason_source =
  let marked, marker_comments, lead_comments, inline_comments =
    print_ocaml_bridge ~kind ~input_name reason_source
  in
  let all_comments = marker_comments @ lead_comments @ inline_comments in
  let render source =
    let source = replace_comment_markers ~input_name source marker_comments in
    let source = restore_leading_comments ~input_name source lead_comments in
    let source =
      try
        render_initial_mlx ~kind ~associative_operators
          ~input_name:output_name ~conf source
      with Ocamlformat_ocaml_common.Syntaxerr.Error error ->
        syntax_failure ~input_name
          ~comments:(marker_comments @ lead_comments)
          source error
    in
    format_mlx ~kind ~input_name:output_name ~conf source
  in
  let source =
    try render marked
    with Failure message
      when String.includes ~affix:"did not stabilize" message
      ->
      let lines =
        comments_before_quoted_string reason_source all_comments
        |> List.map (fun (comment : source_comment) ->
            string_of_int comment.location.loc_start.pos_lnum)
      in
      failwith
        (Printf.sprintf
           "%s: ocamlformat-mlx cannot format the converted output%s. %s"
           input_name
           (if lines = [] then ""
            else
              " (comment before a quoted string at line "
              ^ String.concat ", " lines ^ ")")
           message)
  in
  let source =
    match trailing_arg_leads ~marked ~formatted:source lead_comments with
    | [] -> source
    | comments -> render (own_line_args_to_values marked comments)
  in
  let source =
    realign_comment_continuations source all_comments
  in
  check_format_stable ~kind ~input_name:output_name ~conf source;
  check_comments_preserved ~input_name:output_name source all_comments;
  source

let error_message exn =
  match exn with
  | Reason.Reason_errors.Reason_error (error, loc) ->
      Format.asprintf "%a"
        (fun fmt -> Reason.Reason_errors.report_error fmt ~loc) error
  | Failure message -> message
  | Sys_error message -> message
  | exn -> Printexc.to_string exn

let convert ?(conf = Mlx.Conf.default) ?(associative_operators = [])
    ?(kind = Structure) ?input_name ?output_name source =
  let input_name =
    Option.value input_name
      ~default:(match kind with Structure -> "stdin.re" | Signature -> "stdin.rei")
  in
  let output_name =
    Option.value output_name
      ~default:(match kind with Structure -> "stdout.mlx" | Signature -> "stdout.mli")
  in
  let previous_input_name = !Location.input_name in
  let previous_recoverable = !(Reason.Reason_config.recoverable) in
  Fun.protect
    ~finally:(fun () ->
      Location.input_name := previous_input_name;
      Reason.Reason_config.configure ~recoverable:previous_recoverable)
    (fun () ->
      try
        Ok (convert_exn ~conf ~associative_operators ~kind ~input_name ~output_name source)
      with exn -> Error (error_message exn))
