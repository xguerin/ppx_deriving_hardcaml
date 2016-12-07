#!/usr/bin/env ocaml
#directory "pkg"
#use "topkg.ml"

let ocamlbuild =
  "ocamlbuild -use-ocamlfind -classic-display -plugin-tag"

let () =
  Pkg.describe "ppx_deriving_hardcaml" ~builder:(`Other (ocamlbuild, "_build")) [
    Pkg.lib "pkg/META";
    Pkg.lib ~exts:Exts.library "src/ppx_deriving_hardcaml";
    Pkg.lib ~exts:Exts.module_library "src/ppx_deriving_hardcaml_runtime";
    Pkg.doc "README.md";
    Pkg.doc "LICENSE.txt"; ]