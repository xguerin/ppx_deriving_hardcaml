open Longident
open Location
open Asttypes
open Parsetree
open Ast_helper
open Ast_convenience

let deriver      = "hardcaml"
let raise_errorf = Ppx_deriving.raise_errorf

let wrap_runtime decls =
  Ppx_deriving.sanitize ~module_:(Lident "Ppx_deriving_hardcaml_runtime") decls

let str_of_type ~options ~path ({ ptype_loc = loc } as type_decl) =
  match type_decl.ptype_kind, type_decl.ptype_manifest with
  | Ptype_record labels, _ ->
    raise_errorf ~loc "[%s] str_of_type: this is a record" deriver
  | _ ->
    raise_errorf ~loc "[%s] str_of_type: only supports record types" deriver

let sig_of_type ~options ~path ({ ptype_loc = loc } as type_decl) =
  match type_decl.ptype_kind with
  | Ptype_record _ ->
    let sig_t       = [%type: (string * int) t]
    and sig_map     = [%type: ('a -> 'b) -> 'a t -> 'b t]
    and sig_map2    = [%type: ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t]
    and sig_to_list = [%type: 'a t -> 'a list]
    in
    [
      Sig.value (Val.mk (mknoloc "t") sig_t);
      Sig.value (Val.mk (mknoloc "map") sig_map);
      Sig.value (Val.mk (mknoloc "map2") sig_map2);
      Sig.value (Val.mk (mknoloc "to_list") sig_to_list);
    ]
  | _ -> 
    raise_errorf ~loc "[%s] sig_of_type: only supports record types" deriver

let structure f ~options ~path type_ =
  let (pre, vals) = f ~options ~path type_ in
  match vals with
  | [] -> pre
  | _  -> pre @ [Str.value ?loc:None Recursive vals]

let on_str_decls f ~options ~path type_decls =
  let (pre, vals) = List.split (List.map (f ~options ~path) type_decls) in
  (List.concat pre, List.concat vals)

let on_sig_decls f ~options ~path type_decls =
  List.concat (List.map (f ~options ~path) type_decls)

let () =
  Ppx_deriving.(register
   (create "hardcaml"
    ~type_decl_str:(structure (on_str_decls str_of_type))
    ~type_decl_sig:(on_sig_decls sig_of_type)
    ()
  ))
