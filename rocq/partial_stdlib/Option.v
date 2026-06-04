Require Import mappings.
Axiom option : Type' -> Type'.
Axiom none : forall v17 : Type', option v17.
Axiom some : forall v18 : Type', v18 -> option v18.
