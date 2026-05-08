Require Import Eq.
Require Import HOL.
Require Import mappings.
Axiom funExt : forall v316 : Type', forall v317 : Type', forall v318 : v316 -> v317, forall v319 : v316 -> v317, (forall v321 : v316, (v318 v321) = (v319 v321)) -> v318 = v319.
