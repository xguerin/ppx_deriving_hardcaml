open Longident
open Location
open Asttypes
open Parsetree
open Ast_helper
open Ast_convenience

let deriver      = "hardcaml"
let raise_errorf = Ppx_deriving.raise_errorf

(*
 * Option parsing
 *)

type ext_t = string * Longident.t

type options_t = {
  rtlprefix : Parsetree.expression option;
  rtlsuffix : Parsetree.expression option;
  rtlmangle : bool;
  extends   : ext_t list;
}

let rec parse_extends = function
  | [%expr []] -> []
  | [%expr ([%e? { pexp_desc = Pexp_constant (Pconst_string (name, _)) }],
            [%e? { pexp_desc = Pexp_construct ({ txt = mdl }, _) }])
           :: [%e? tl]] -> (name, mdl) :: (parse_extends tl)
  | expr -> raise_errorf ~loc:expr.pexp_loc "%s unsupported extends format" deriver

let parse_options options =
  List.fold_left
    (fun agg (name, expr) ->
       match name with
       | "rtlprefix" -> { agg with rtlprefix = Some(expr) }
       | "rtlsuffix" -> { agg with rtlsuffix = Some(expr) }
       | "rtlmangle" ->
         begin match expr with
           | [%expr true] -> { agg with rtlmangle = true }
           | [%expr false] -> { agg with rtlmangle = false }
           | _ -> raise_errorf ~loc:expr.pexp_loc "[%s] rtlmangle option must be a boolean" deriver
         end
       | "extends" -> { agg with extends = parse_extends expr }
       | _ -> raise_errorf ~loc:expr.pexp_loc "%s unsupported option %s" deriver name)
    { rtlprefix = None; rtlsuffix = None; rtlmangle = false; extends = [] }
    options

(*
 * Attribute definition and parsing
 *)

let attr_bits attrs =
  Ppx_deriving.(attrs |> attr ~deriver "bits" |> Arg.(get_attr ~deriver expr))

let attr_length attrs =
  Ppx_deriving.(attrs |> attr ~deriver "length" |> Arg.(get_attr ~deriver expr))

let attr_rtlname attrs =
  Ppx_deriving.(attrs |> attr ~deriver "rtlname" |> Arg.(get_attr ~deriver expr))

let attr_rtlprefix attrs =
  Ppx_deriving.(attrs |> attr ~deriver "rtlprefix" |> Arg.(get_attr ~deriver expr))

let attr_rtlsuffix attrs =
  Ppx_deriving.(attrs |> attr ~deriver "rtlsuffix" |> Arg.(get_attr ~deriver expr))

let attr_rtlmangle attrs =
  Ppx_deriving.(attrs |> attr ~deriver "rtlmangle" |> Arg.(get_attr ~deriver expr))

let get_bits ~loc attrs =
  match attr_bits attrs with
  | Some (expr) -> expr
  | None -> Exp.constant (Pconst_integer ("1", None))

let get_length ~loc attrs =
  match attr_length attrs with
  | Some (expr) -> expr
  | None -> raise_errorf ~loc "[%s] length attribute must be set" deriver

let get_rtlname ~loc txt attrs =
  match attr_rtlname attrs with
  | Some (expr) -> expr
  | None -> Exp.constant (Pconst_string (txt, None))

let get_rtlprefix ~loc opts attrs =
  match attr_rtlprefix attrs with
  | Some (expr) -> Some (expr)
  | None -> opts.rtlprefix

let get_rtlsuffix ~loc opts attrs =
  match attr_rtlsuffix attrs with
  | Some (expr) -> Some (expr)
  | None -> opts.rtlsuffix

let get_rtlmangle ~loc opts attrs =
  match attr_rtlmangle attrs with
  | Some ([%expr true]) -> true
  | Some ([%expr false]) -> false
  | Some (_) -> raise_errorf ~loc "[%s] rtlmangle attribute must be a boolean" deriver
  | None -> opts.rtlmangle

(*
 * Identifier manipulation
 *)

let mk_rtlident ~loc name prefix suffix =
  match prefix, suffix with
  | None      , None       -> [%expr               ([%e name])]
  | Some (pre), None       -> [%expr ([%e pre])  ^ ([%e name])]
  | None      , Some (suf) -> [%expr               ([%e name]) ^ ([%e suf])]
  | Some (pre), Some (suf) -> [%expr ([%e pre])  ^ ([%e name]) ^ ([%e suf])]
  [@metaloc loc]

let mangle_name ~loc name mangle =
  if mangle then [%expr [%e name] ^ "_" ^ _n] else [%expr _n]

(*
 * Extension generation utilities
 *)

let make_ext_sig ~loc (name, mdl) =
  let id = Mty.ident (mkloc (Ldot (mdl, "Ex")) loc)
  and tn = mkloc (Lident "t") loc
  and ty = Type.mk
      ~params:[ (Typ.var "a", Invariant) ]
      ~kind:Ptype_abstract
      ~priv:Public
      ~manifest:[%type: 'a t]
      (mkloc "t" loc)
  in
  [ Pwith_type (tn, ty) ]
  |> Mty.with_ id |> Md.mk (mkloc name loc) |> Sig.module_

let make_ext_str ~loc (name, mdl) =
  let id = Mod.ident (mkloc (Ldot (mdl, "Ex")) loc) in
  [
    [%stri type 'a x = 'a t];
    [%stri type 'a t = 'a x];
    [%stri let t = t];
    [%stri let map = map];
    [%stri let map2 = map2];
    [%stri let to_list = to_list];
  ]
  |> Mod.structure |> Mod.apply id |> Mb.mk (mkloc name loc) |> Str.module_

(*
 * Code generation utility functions
 *)

let check_list_and_array_label var loc = function
  | Ptyp_var v
  | Ptyp_constr ({ txt = Ldot(_, _) }, [ { ptyp_desc = Ptyp_var(v) } ]) when v = var ->
    ()
  | _ ->
    raise_errorf ~loc "[%s] check_label: only supports abstract record labels" deriver

let check_label var ({ pld_name = { txt; loc; } } as label) =
  match label.pld_type.ptyp_desc with
  | Ptyp_var v
  | Ptyp_constr ({ txt = Ldot(_, _) }, [ { ptyp_desc = Ptyp_var(v) } ]) when v = var ->
    ()
  | Ptyp_constr ({ txt = Lident("list") }, [ { ptyp_desc } ])
  | Ptyp_constr ({ txt = Lident("array") }, [ { ptyp_desc } ]) ->
    check_list_and_array_label var loc ptyp_desc
  | _ ->
    raise_errorf ~loc "[%s] check_label: only supports abstract record labels" deriver

let expand_array_init ~loc vname attrs =
  let nbits = get_bits ~loc attrs in
  let length = get_length ~loc attrs in
  [%expr Array.init [%e length] (fun _i -> (([%e vname] ^ (string_of_int _i)), [%e nbits]))]

let expand_array_init_str ~loc vname mapid mid attrs =
  let length = get_length ~loc attrs in
  [%expr Array.init [%e length] (fun _i ->
      [%e mapid] (fun (_n, _b) -> ([%e vname], _b)) [%e Exp.ident mid])]

(*
 * Expand t label
 *)

let expand_t_label_array var loc attrs name prefix suffix mangle = function
  (* 'a *)
  | Ptyp_var(v) when v = var ->
    let rtlident = mk_rtlident ~loc name prefix suffix in
    expand_array_init ~loc rtlident attrs
  (* 'a Module.t *)
  | Ptyp_constr (({ txt = Ldot(mname, _) } as mid), [ { ptyp_desc = Ptyp_var(v) } ]) when v = var ->
    let mangled = [%expr [%e mangle_name ~loc name mangle] ^ (string_of_int _i)] in
    let rtlident = mk_rtlident ~loc mangled prefix suffix in
    let mapid = Exp.ident (mkloc (Ldot (mname, "map")) loc) in
    expand_array_init_str ~loc rtlident mapid mid attrs
  (* Default *)
  | _ ->
    raise_errorf ~loc "[%s] expand_t_label_array: only supports abstract record labels" deriver

let expand_t_label_list var loc attrs name prefix suffix mangle desc =
  let ainit = expand_t_label_array var loc attrs name prefix suffix mangle desc in
  [%expr Array.to_list ([%e ainit])]

let expand_t_label opts var { pld_name = { txt; loc; }; pld_type; pld_attributes; } =
  let rtlname = get_rtlname ~loc txt pld_attributes
  and rtlprefix = get_rtlprefix ~loc opts pld_attributes
  and rtlsuffix = get_rtlsuffix ~loc opts pld_attributes
  and rtlmangle = get_rtlmangle ~loc opts pld_attributes
  in
  let expr = match pld_type.ptyp_desc with
    (* 'a *)
    | Ptyp_var v when v = var ->
      let nbits = get_bits ~loc pld_attributes
      and rtlident = mk_rtlident ~loc rtlname rtlprefix rtlsuffix in
      Exp.tuple [ rtlident; nbits ]
    (* 'a Module.t *)
    | Ptyp_constr (({ txt = Ldot(mname, _) } as mid), [ { ptyp_desc = Ptyp_var(v) } ]) when v = var ->
      let mangled = mangle_name ~loc rtlname rtlmangle in
      let rtlident = mk_rtlident ~loc mangled rtlprefix rtlsuffix in
      let mapid = Exp.ident (mkloc (Ldot (mname, "map")) loc) in
      [%expr [%e mapid] (fun (_n, _b) -> [%e rtlident], _b) [%e Exp.ident mid]]
    (* 'a list, 'a Module.t list *)
    | Ptyp_constr ({ txt = Lident("list") }, [ { ptyp_desc } ]) ->
      expand_t_label_list var loc pld_attributes rtlname rtlprefix rtlsuffix rtlmangle ptyp_desc
    (* 'a array, 'a Module.t array *)
    | Ptyp_constr ({ txt = Lident("array") }, [ { ptyp_desc } ]) ->
      expand_t_label_array var loc pld_attributes rtlname rtlprefix rtlsuffix rtlmangle ptyp_desc
    (* Default *)
    | _ ->
      raise_errorf ~loc "[%s] expand_t_label: only supports abstract record labels" deriver
  in
  (mknoloc (Lident txt), expr)

(*
 * Expand map label
 *)

let mkfield var memb =
  Exp.field (Exp.ident (mknoloc (Lident(var)))) (mknoloc (Lident(memb)))

let expand_map_label_list var loc ident = function
  (* 'a *)
  | Ptyp_var(v) when v = var ->
    [%expr List.map f [%e ident]]
  (* 'a Module.t *)
  | Ptyp_constr ({ txt = Ldot(mname, _) }, [ { ptyp_desc = Ptyp_var(v) } ]) when v = var ->
    let mapid = Exp.ident (mkloc (Ldot (mname, "map")) loc) in
    [%expr List.map (fun _e -> [%e mapid] f _e) [%e ident]]
  (* Default *)
  | _ ->
    raise_errorf ~loc "[%s] expand_map_label_list: only supports abstract record labels" deriver

let expand_map_label_array var loc ident = function
  (* 'a *)
  | Ptyp_var(v) when v = var ->
    [%expr Array.map f [%e ident]]
  (* 'a Module.t *)
  | Ptyp_constr ({ txt = Ldot(mname, _) }, [ { ptyp_desc = Ptyp_var(v) } ]) when v = var ->
    let mapid = Exp.ident (mkloc (Ldot (mname, "map")) loc) in
    [%expr Array.map (fun _e -> [%e mapid] f _e) [%e ident]]
  (* Default *)
  | _ ->
    raise_errorf ~loc "[%s] expand_map_label_list: only supports abstract record labels" deriver

let expand_map_label opts var ({ pld_name = { txt; loc; } } as label) =
  let ident = mkfield "x" txt in
  let expr = match label.pld_type.ptyp_desc with
    (* 'a *)
    | Ptyp_var v when v = var ->
      [%expr f [%e ident]]
    (* 'a Module.t *)
    | Ptyp_constr ({ txt = Ldot(mname, _) }, [ { ptyp_desc = Ptyp_var(v) } ]) when v = var ->
      let mapid = Exp.ident (mkloc (Ldot (mname, "map")) loc) in
      [%expr [%e mapid] f [%e ident]]
    (* 'a list, 'a Module.t list *)
    | Ptyp_constr ({ txt = Lident("list") }, [ { ptyp_desc } ]) ->
      expand_map_label_list var loc ident ptyp_desc
    (* 'a array, 'a Module.t array *)
    | Ptyp_constr ({ txt = Lident("array") }, [ { ptyp_desc } ]) ->
      expand_map_label_array var loc ident ptyp_desc
    (* Default *)
    | _ ->
      raise_errorf ~loc "[%s] expand_map_label: only supports abstract record labels" deriver
  in
  (mknoloc (Lident txt), expr)

(*
 * Expand map2 label
 *)

let expand_map2_label_list var loc ident0 ident1 = function
  (* 'a *)
  | Ptyp_var(v) when v = var ->
    [%expr List.map2 f [%e ident0] [%e ident1]]
  (* 'a Module.t *)
  | Ptyp_constr ({ txt = Ldot(mname, _) }, [ { ptyp_desc = Ptyp_var(v) } ]) when v = var ->
    let mapid = Exp.ident (mkloc (Ldot (mname, "map2")) loc) in
    [%expr List.map2 (fun _e0 _e1 -> [%e mapid] f _e0 _e1) [%e ident0] [%e ident1]]
  (* Default *)
  | _ ->
    raise_errorf ~loc "[%s] expand_map_label_list: only supports abstract record labels" deriver

let expand_map2_label_array var loc ident0 ident1 = function
  (* 'a *)
  | Ptyp_var(v) when v = var ->
    [%expr Array.init (Array.length [%e ident0])
        (fun _i -> f (Array.get [%e ident0] _i) (Array.get [%e ident1] _i))]
  (* 'a Module.t *)
  | Ptyp_constr ({ txt = Ldot(mname, _) }, [ { ptyp_desc = Ptyp_var(v) } ]) when v = var ->
    let mapid = Exp.ident (mkloc (Ldot (mname, "map2")) loc) in
    [%expr Array.init (Array.length [%e ident0])
        (fun _i -> [%e mapid] f (Array.get [%e ident0] _i) (Array.get [%e ident1] _i))]
  (* Default *)
  | _ ->
    raise_errorf ~loc "[%s] expand_map_label_list: only supports abstract record labels" deriver

let expand_map2_label opts var ({ pld_name = { txt; loc; } } as label) =
  let ident0 = mkfield "x0" txt in
  let ident1 = mkfield "x1" txt in
  let expr = match label.pld_type.ptyp_desc with
    (* 'a *)
    | Ptyp_var v when v = var ->
      [%expr f [%e ident0] [%e ident1]]
    (* 'a Module.t *)
    | Ptyp_constr ({ txt = Ldot(mname, _) }, [ { ptyp_desc = Ptyp_var(v) } ]) when v = var ->
      let mapid = Exp.ident (mkloc (Ldot (mname, "map2")) loc) in
      [%expr [%e mapid] f [%e ident0] [%e ident1]]
    (* 'a list, 'a Module.t list *)
    | Ptyp_constr ({ txt = Lident("list") }, [ { ptyp_desc } ])  ->
      expand_map2_label_list var loc ident0 ident1 ptyp_desc
    (* 'a array, 'a Module.t array *)
    | Ptyp_constr ({ txt = Lident("array") }, [ { ptyp_desc } ]) ->
      expand_map2_label_array var loc ident0 ident1 ptyp_desc
    (* Default *)
    | _ ->
      raise_errorf ~loc "[%s] expand_map2_label: only supports abstract record labels" deriver
  in
  (mknoloc (Lident txt), expr)

(*
 * Expand to_list label
 *)

let expand_to_list_label_list var loc ident = function
  (* 'a *)
  | Ptyp_var(v) when v = var ->
    ident
  (* 'a Module.t *)
  | Ptyp_constr ({ txt = Ldot(mname, _) }, [ { ptyp_desc = Ptyp_var(v) } ]) when v = var ->
    let to_list_id = Exp.ident (mkloc (Ldot (mname, "to_list")) loc) in
    [%expr List.flatten (List.map (fun _e -> [%e to_list_id] _e) [%e ident])]
  (* Default *)
  | _ ->
    raise_errorf ~loc "[%s] expand_map_label_list: only supports abstract record labels" deriver

let expand_to_list_label_array var loc ident desc =
  expand_to_list_label_list var loc [%expr Array.to_list [%e ident]] desc

let expand_to_list_label opts var ({ pld_name = { txt; loc; } } as label) =
  let ident = mkfield "x" txt in
  match label.pld_type.ptyp_desc with
  (* 'a *)
  | Ptyp_var v when v = var ->
    [%expr [ [%e ident] ]]
  (* 'a Module.t *)
  | Ptyp_constr ({ txt = Ldot(mname, _) }, [ { ptyp_desc = Ptyp_var(v) } ]) when v = var ->
    Exp.apply (Exp.ident (mkloc (Ldot (mname, "to_list")) loc)) [ (Nolabel, ident) ]
  (* 'a list, 'a Module.t list *)
  | Ptyp_constr ({ txt = Lident("list") }, [ { ptyp_desc } ]) ->
    expand_to_list_label_list var loc ident ptyp_desc
  (* 'a array, 'a Module.t array *)
  | Ptyp_constr ({ txt = Lident("array") }, [ { ptyp_desc } ]) ->
    expand_to_list_label_array var loc ident ptyp_desc
  (* Default *)
  | _ ->
    raise_errorf ~loc "[%s] expand_to_list_label: only supports abstract record labels" deriver

let build_to_list_args labels =
  List.fold_right
    (fun expr acc -> Exp.construct
         (mknoloc (Lident "::"))
         (Some (Exp.tuple [ expr; acc ])))
    labels
    (Exp.construct (mknoloc (Lident "[]")) None)

(*
 * PPX deriving
 *)

let str_of_type ~options ~path ({ ptype_loc = loc } as type_decl) =
  let opts = parse_options options in
  match type_decl.ptype_kind, type_decl.ptype_params, type_decl.ptype_manifest with
  | Ptype_record labels, [ ({ ptyp_desc = Ptyp_var(var) }, _) ], None ->
    let str_t_labels       = List.map (expand_t_label opts var) labels in
    let str_t              = Exp.record str_t_labels None in
    let str_map_labels     = List.map (expand_map_label opts var) labels in
    let str_map            = [%expr fun f x -> [%e Exp.record str_map_labels None]] in
    let str_map2_labels    = List.map (expand_map2_label opts var) labels in
    let str_map2           = [%expr fun f x0 x1 -> [%e Exp.record str_map2_labels None]] in
    let str_to_list_labels = List.map (expand_to_list_label opts var) labels in
    let str_to_list_args   = build_to_list_args str_to_list_labels in
    let str_to_list        = [%expr fun x -> List.concat [%e str_to_list_args]] in
    let str_expands        = List.map (make_ext_str ~loc) opts.extends in
    [
      Str.value Nonrecursive [Vb.mk (pvar "t"      ) str_t      ];
      Str.value Nonrecursive [Vb.mk (pvar "map"    ) str_map    ];
      Str.value Nonrecursive [Vb.mk (pvar "map2"   ) str_map2   ];
      Str.value Nonrecursive [Vb.mk (pvar "to_list") str_to_list];
    ]
    @ str_expands
  | _ ->
    raise_errorf ~loc "[%s] str_of_type: only supports record types" deriver

let sig_of_type ~options ~path ({ ptype_loc = loc } as type_decl) =
  let opts = parse_options options in
  match type_decl.ptype_kind, type_decl.ptype_params with
  | Ptype_record labels, [ ({ ptyp_desc = Ptyp_var(v) }, _) ] ->
    List.iter (check_label v) labels;
    let sig_t       = [%type: (string * int) t]
    and sig_map     = [%type: ('a -> 'b) -> 'a t -> 'b t]
    and sig_map2    = [%type: ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t]
    and sig_to_list = [%type: 'a t -> 'a list]
    and sig_expands = List.map (make_ext_sig ~loc) opts.extends
    in
    [
      Sig.value (Val.mk (mknoloc "t"      ) sig_t      );
      Sig.value (Val.mk (mknoloc "map"    ) sig_map    );
      Sig.value (Val.mk (mknoloc "map2"   ) sig_map2   );
      Sig.value (Val.mk (mknoloc "to_list") sig_to_list);
    ]
    @ sig_expands
  | _, _ ->
    raise_errorf ~loc "[%s] sig_of_type: only supports record types" deriver

let on_str_decls f ~options ~path type_decls =
  List.concat (List.map (f ~options ~path) type_decls)

let on_sig_decls f ~options ~path type_decls =
  List.concat (List.map (f ~options ~path) type_decls)

let () =
  Ppx_deriving.(register (create deriver
    ~type_decl_str:(on_str_decls str_of_type)
    ~type_decl_sig:(on_sig_decls sig_of_type)
    ()
  ))
