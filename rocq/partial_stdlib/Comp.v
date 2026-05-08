Require Import Bool.
Require Import Eq.
Require Import FOL.
Require Import mappings.
Definition lp_Lt_u2260_Eq : @neq comparison' Lt Eq := fun v801 : Lt = Eq => @ind_eq comparison' Lt Eq v801 (fun v802 : comparison' => Is_true (isEq v802)) I.
Definition lp_Gt_u2260_Eq : @neq comparison' Gt Eq := fun v803 : Gt = Eq => @ind_eq comparison' Gt Eq v803 (fun v804 : comparison' => Is_true (isEq v804)) I.
Definition lp_Gt_u2260_Lt : @neq comparison' Gt Lt := fun v805 : Gt = Lt => @ind_eq comparison' Gt Lt v805 (fun v806 : comparison' => Is_true (isLt v806)) I.
Definition opp_idem : forall v808 : comparison', (CompOpp (CompOpp v808)) = v808 := ind_Comp (fun v809 : comparison' => (CompOpp (CompOpp v809)) = v809) (@eq_refl comparison' (CompOpp (CompOpp Eq))) (@eq_refl comparison' (CompOpp (CompOpp Lt))) (@eq_refl comparison' (CompOpp (CompOpp Gt))).
