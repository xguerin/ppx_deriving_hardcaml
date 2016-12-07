# `ppx_deriving` Plugin for HardCaml

This module implements a plugin for the `ppx_deriving` rewriter that supports the HardCaml syntax:

* Provide a `record` annotation to generate helper functions
* Provide an optional `bits` attribute for signals
* Provide a required `width` attribute for `list` and `array`

## Examples

### Module interface

Original syntax:

```ocaml
module S : interface
  signal
  signal_list{ }
  signal_array{| |}
end
```

New syntax:

```ocaml
module S : sig
  type 'a t = {
    signal       : 'a;
    signal_list  : 'a list;
    signal_array : 'a array;
  } [@@deriving hardcaml]
end
```

### Module implementation

Original syntax:

```ocaml
module S = interface
  signal[2]
  signal_list{2}[4]
  signal_array{|2|}[4]
end
```

New syntax:

```ocaml
module S = struct
  type 'a t = {
    signal       : 'a       [@bits 2];
    signal_list  : 'a list  [@length 2][@bits 4];
    signal_array : 'a array [@length 2][@bits 4];
  } [@@deriving hardcaml]
end
```
