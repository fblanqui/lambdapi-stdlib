Require Import Eq.
Require Import FOL.
Require Import mappings.

(* The direct translated Bool proof file does not currently check against
   native Rocq bool. The checked Bool interface used by this slice lives in
   mappings.v, where the Lambdapi Bool symbols are mapped to native Rocq
   definitions and proved shim lemmas. *)
