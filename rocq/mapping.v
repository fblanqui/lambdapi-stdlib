From Stdlib Require Export Classical_Prop ClassicalEpsilon Bool Nat List.

(* Prop *)

Definition imp (p q : Prop) : Prop := p -> q.

(* Set *)

Record Type' := { type :> Type; el : type }.

(* FOL *)

Definition all {a : Type'} (P: a -> Prop) : Prop := forall x:a, P x.

(* HOL *)

Definition arr a (b : Type') := {| type := a -> b; el := fun _ => el b |}.
Canonical arr.

(* Eq *)

Lemma ind_eq : forall {a : Type'} {x y : a}, (x = y) -> forall p, (p y) -> p x.
Proof.
  intros a x y e p py. rewrite e. exact py.
Qed.
Definition neq {a : Type'} (x y : a) := ~ (x = y).

(* Bool *)

Definition bool' := {| type := bool ; el := true|}.
Canonical bool'.
							 
Definition if' (b : bool) {a : Type'} (e1 : a) (e2 : a) := 
    if b then e1 else e2.

(* Comp *)

Definition comparison' := {| type := comparison ; el := Eq|}.

Definition isEq (c : comparison) := 
 match c with
 | Eq => true
 | _ => false
 end.
						      
Definition isLt (c : comparison) := 
 match c with
 | Lt => true
 | _ => false
 end.	

Definition isGt (c : comparison) := 
 match c with
 | Gt => true
 | _ => false
 end.		       

Definition case_Comp := fun (A : Type') (c : comparison') (x y z : A) =>
match c with
| Eq => x
| Lt => y
| Gt => z
end.
				       
(* Epsilon *)

Definition eps : forall {A : Type'}, (type A -> Prop) -> type A :=
  fun A P => epsilon (inhabits (el A)) P.
  
Lemma eps_spec {A : Type'} {P : type A -> Prop} : (exists x, P x) -> P (eps P).
Proof. intro h. unfold eps. apply epsilon_spec. exact h. Qed.

(* Prod *)

Definition prod' (A B : Type')
  := {| type := prod A B; el := pair (el A) (el B) |}.
Canonical prod'.

(* Subset *)

(*Definition subset (A : Type') (P: A -> Prop) (h: @ex A (fun x : A => P x)): Type'.
Proof.
Defined.*)
