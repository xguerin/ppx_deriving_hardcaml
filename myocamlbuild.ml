open Ocamlbuild_plugin

let () = dispatch (fun phase ->
  match phase with
  | After_rules ->
    let ppx_deriving_component deriver =
      (Findlib.query "ppx_deriving").Findlib.location ^ "/" ^ deriver
    in
    flag ["ocaml"; "compile"; "use_hardcaml"] &
      S[A"-ppx"; A"ocamlfind ppx_import/ppx_import";
        A"-ppx"; A("ocamlfind ppx_deriving/ppx_deriving "^
                   "src/ppx_deriving_hardcaml.cma "^
                   (ppx_deriving_component "ppx_deriving_show.cma"));
        A"-I"; A(ppx_deriving_component "")];
    flag ["ocaml"; "link"; "use_hardcaml"; "byte"] &
      A(ppx_deriving_component "ppx_deriving_runtime.cma");
    flag ["ocaml"; "link"; "use_hardcaml"; "native"] &
      A(ppx_deriving_component "ppx_deriving_runtime.cmxa");
    ocaml_lib ~dir:"src" "src/ppx_deriving_hardcaml_runtime";

  | _ -> ())