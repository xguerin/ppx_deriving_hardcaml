#!/usr/bin/env ocaml
#directory "pkg"
#use "topkg.ml"

let ocamlbuild =
  "ocamlbuild -use-ocamlfind -classic-display -plugin-tag"
let () =
  Pkg.describe "ppx_deriving_hardcaml" ~builder:(`OCamlbuild) [
    Pkg.lib "pkg/META";
    Pkg.lib ~exts:Exts.library "src/ppx_deriving_hardcaml";
    Pkg.doc "README.md";
    Pkg.doc "LICENSE.txt";
  ]
