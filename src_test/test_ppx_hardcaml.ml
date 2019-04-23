open OUnit2

type 'a t =
  { field : 'a; } [@@deriving hardcaml]

let () =
  Printf.printf "Nothing yet.\n"
