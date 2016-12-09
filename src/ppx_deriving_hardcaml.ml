open Longident
open Location
open Asttypes
open Parsetree
open Ast_helper
open Ast_convenience

let deriver      = "hardcaml"
let raise_errorf = Ppx_deriving.raise_errorf

let parse_options options =
  options |> List.iter (fun (name, expr) ->
    match name with
    | _ -> raise_errorf ~loc:expr.pexp_loc "%s does not support option %s" deriver name)

let attr_bits attrs =
  Ppx_deriving.(attrs |> attr ~deriver "bits" |> Arg.(get_attr ~deriver expr))

let attr_length attrs =
  Ppx_deriving.(attrs |> attr ~deriver "length" |> Arg.(get_attr ~deriver expr))

let get_bits ~loc attrs = 
  match attr_bits attrs with
  | Some (({ pexp_desc = Pexp_constant (Pconst_integer (_, _)) } as iconst)) ->
    iconst
  | Some _ ->
    raise_errorf ~loc "[%s] bits attribute only supports integers" deriver
  | None ->
    Exp.constant (Pconst_integer ("1", None))

let get_length ~loc attrs = 
  match attr_length attrs with
  | Some (({ pexp_desc = Pexp_constant (Pconst_integer (_, _)) } as iconst)) ->
    iconst
  | Some _ ->
    raise_errorf ~loc "[%s] length attribute only supports integers" deriver
  | None ->
    raise_errorf ~loc "[%s] length attribute must be set" deriver

let check_label var ({ pld_name = { txt; loc; } } as label) =
  match label.pld_type.ptyp_desc with
  | Ptyp_var v
  | Ptyp_constr ({ txt = Lident("list") }, [ { ptyp_desc = Ptyp_var(v) } ])
  | Ptyp_constr ({ txt = Lident("array") }, [ { ptyp_desc = Ptyp_var(v) } ]) when v = var ->
    ()
  | _ -> 
    raise_errorf ~loc "[%s] check_label: only supports abstract record labels" deriver

let expand_array_init ~loc txt attrs =
  let nbits = get_bits ~loc attrs in
  let length = get_length ~loc attrs in
  let vname = Exp.constant (Pconst_string (txt, None)) in
  [%expr Array.init [%e length] (fun _i -> (([%e vname] ^ (string_of_int _i)), [%e nbits]))]

let expand_t_label var ({ pld_name = { txt; loc; } } as label) =
  let expr = match label.pld_type.ptyp_desc with
    | Ptyp_var v when v = var ->
      let nbits = get_bits ~loc label.pld_attributes in
      Exp.tuple [ Exp.constant (Pconst_string (txt, None)); nbits ]
    | Ptyp_constr ({ txt = Lident("list") }, [ { ptyp_desc = Ptyp_var(v) } ]) when v = var ->
      let ainit = expand_array_init ~loc txt label.pld_attributes in
      [%expr Array.to_list ([%e ainit])]
    | Ptyp_constr ({ txt = Lident("array") }, [ { ptyp_desc = Ptyp_var(v) } ]) when v = var ->
      expand_array_init ~loc txt label.pld_attributes
    | Ptyp_constr (({ txt = Ldot(_, _) } as mid), [ { ptyp_desc = Ptyp_var(v) } ]) when v = var ->
      Exp.ident mid
    | _ -> 
      raise_errorf ~loc "[%s] expand_t_label: only supports abstract record labels" deriver
  in
  (mknoloc (Lident txt), expr)

let mkfield var memb = 
  Exp.field (Exp.ident (mknoloc (Lident(var)))) (mknoloc (Lident(memb)))

let expand_map_label var ({ pld_name = { txt; loc; } } as label) =
  let ident = mkfield "x" txt in
  let expr = match label.pld_type.ptyp_desc with
    | Ptyp_var v when v = var ->
      [%expr f [%e ident]]
    | Ptyp_constr ({ txt = Lident("list") }, [ { ptyp_desc = Ptyp_var(v) } ]) when v = var ->
      [%expr List.map f [%e ident]]
    | Ptyp_constr ({ txt = Lident("array") }, [ { ptyp_desc = Ptyp_var(v) } ]) when v = var ->
      [%expr Array.map f [%e ident]]
    | Ptyp_constr ({ txt = Ldot(mname, _) }, [ { ptyp_desc = Ptyp_var(v) } ]) when v = var ->
      let mapid = Exp.ident (mkloc (Ldot (mname, "map")) loc) in
      [%expr [%e mapid] f [%e ident]]
    | _ -> 
      raise_errorf ~loc "[%s] expand_map_label: only supports abstract record labels" deriver
  in
  (mknoloc (Lident txt), expr)

let expand_map2_label var ({ pld_name = { txt; loc; } } as label) =
  let ident0 = mkfield "x0" txt in
  let ident1 = mkfield "x1" txt in
  let expr = match label.pld_type.ptyp_desc with
    | Ptyp_var v when v = var ->
      [%expr f [%e ident0] [%e ident1]]
    | Ptyp_constr ({ txt = Lident("list") }, [ { ptyp_desc = Ptyp_var(v) } ]) when v = var ->
      [%expr List.map2 f [%e ident0] [%e ident1]]
    | Ptyp_constr ({ txt = Lident("array") }, [ { ptyp_desc = Ptyp_var(v) } ]) when v = var ->
      [%expr Array.init (Array.length [%e ident0])
          (fun _i -> f (Array.get [%e ident0] _i) (Array.get [%e ident1] _i))]
    | Ptyp_constr ({ txt = Ldot(mname, _) }, [ { ptyp_desc = Ptyp_var(v) } ]) when v = var ->
      let mapid = Exp.ident (mkloc (Ldot (mname, "map2")) loc) in
      [%expr [%e mapid] f [%e ident0] [%e ident1]]
    | _ -> 
      raise_errorf ~loc "[%s] expand_map2_label: only supports abstract record labels" deriver
  in
  (mknoloc (Lident txt), expr)

let expand_to_list_label var ({ pld_name = { txt; loc; } } as label) =
  let ident = mkfield "x" txt in
  match label.pld_type.ptyp_desc with
    | Ptyp_var v when v = var ->
      [%expr [ [%e ident] ]]
    | Ptyp_constr ({ txt = Lident("list") }, [ { ptyp_desc = Ptyp_var(v) } ]) when v = var ->
      ident
    | Ptyp_constr ({ txt = Lident("array") }, [ { ptyp_desc = Ptyp_var(v) } ]) when v = var ->
      [%expr Array.to_list [%e ident]]
    | Ptyp_constr ({ txt = Ldot(mname, _) }, [ { ptyp_desc = Ptyp_var(v) } ]) when v = var ->
      Exp.apply (Exp.ident (mkloc (Ldot (mname, "to_list")) loc)) [ (Nolabel, ident) ]
    | _ -> 
      raise_errorf ~loc "[%s] expand_to_list_label: only supports abstract record labels" deriver

let build_to_list_args labels =
  List.fold_right 
    (fun expr acc -> Exp.construct
         (mknoloc (Lident "::"))
         (Some (Exp.tuple [ expr; acc ])))
    labels
    (Exp.construct (mknoloc (Lident "[]")) None)

let str_of_type ~options ~path ({ ptype_loc = loc } as type_decl) =
  parse_options options;
  match type_decl.ptype_kind, type_decl.ptype_params, type_decl.ptype_manifest with
  | Ptype_record labels, [ ({ ptyp_desc = Ptyp_var(var) }, _) ], None ->
    let str_t_labels       = List.map (expand_t_label var) labels in
    let str_t              = Exp.record str_t_labels None in
    let str_map_labels     = List.map (expand_map_label var) labels in
    let str_map            = [%expr fun f x -> [%e Exp.record str_map_labels None]] in
    let str_map2_labels    = List.map (expand_map2_label var) labels in
    let str_map2           = [%expr fun f x0 x1 -> [%e Exp.record str_map2_labels None]] in
    let str_to_list_labels = List.map (expand_to_list_label var) labels in
    let str_to_list_args   = build_to_list_args str_to_list_labels in
    let str_to_list        = [%expr fun x -> List.concat [%e str_to_list_args]] in
    [
      Vb.mk (pvar "t")       str_t;
      Vb.mk (pvar "map")     str_map;
      Vb.mk (pvar "map2")    str_map2;
      Vb.mk (pvar "to_list") str_to_list;
    ]
  | _ ->
    raise_errorf ~loc "[%s] str_of_type: only supports record types" deriver

let sig_of_type ~options ~path ({ ptype_loc = loc } as type_decl) =
  parse_options options;
  match type_decl.ptype_kind, type_decl.ptype_params with
  | Ptype_record labels, [ ({ ptyp_desc = Ptyp_var(v) }, _) ] ->
    List.iter (check_label v) labels;
    let sig_t       = [%type: (string * int) t]
    and sig_map     = [%type: ('a -> 'b) -> 'a t -> 'b t]
    and sig_map2    = [%type: ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t]
    and sig_to_list = [%type: 'a t -> 'a list]
    in
    [
      Sig.value (Val.mk (mknoloc "t")       sig_t);
      Sig.value (Val.mk (mknoloc "map")     sig_map);
      Sig.value (Val.mk (mknoloc "map2")    sig_map2);
      Sig.value (Val.mk (mknoloc "to_list") sig_to_list);
    ]
  | _, _ -> 
    raise_errorf ~loc "[%s] sig_of_type: only supports record types" deriver

let on_str_decls f ~options ~path type_decls =
  List.map (fun decl -> Str.value Nonrecursive (f ~options ~path decl)) type_decls

let on_sig_decls f ~options ~path type_decls =
  List.concat (List.map (f ~options ~path) type_decls)

let () =
  Ppx_deriving.(register (create deriver
    ~type_decl_str:(on_str_decls str_of_type)
    ~type_decl_sig:(on_sig_decls sig_of_type)
    ()
  ))
