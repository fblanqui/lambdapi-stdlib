// Prop
builtin "Prop" ≔ Props.Prop;
builtin "True" ≔ Props.{|⊤|};
builtin "I" ≔ Props.{|⊤ᵢ|};
builtin "False" ≔ Props.{|⊥|};
builtin "False_ind" ≔ Props.{|⊥ₑ|};
builtin "imp" ≔ Props.{|⇒|};
builtin "not" ≔ Props.{|¬|};
builtin "and" ≔ Props.{|∧|};
builtin "@conj" ≔ Props.{|∧ᵢ|};
builtin "@proj1" ≔ Props.{|∧ₑ₁|};
builtin "@proj2" ≔ Props.{|∧ₑ₂|};
builtin "\/" ≔ Props.{|∨|};
builtin "@or_introl" ≔ Props.{|∨ᵢ₁|};
builtin "@or_intror" ≔ Props.{|∨ᵢ₂|};
builtin "@ex_intro" ≔ Props.{|∃ᵢ|};
builtin "@ex_elim" ≔ Props.{|∃ₑ|};
builtin "iff" ≔ Props.{|⇔|};

// Set
builtin "Type'" ≔ Sets.Set;
builtin "nat" ≔ Sets.{|ι|};
builtin "el" ≔ Sets.el;

// Prod
builtin "prod" ≔ Prod.Prod;
builtin "prod" ≔ Prod.{|×|};
builtin "@pair" ≔ Prod.{|‚|};
builtin "@fst" ≔ Prod.{|₁|};
builtin "@snd" ≔ Prod.{|₂|};

// FOL
builtin "@all" ≔ FOL.{|∀|};
builtin "@ex" ≔ FOL.{|∃|};

// HOL
builtin "arr" ≔ HOL.{|⤳|};

// Eq
builtin "@eq" ≔ Eq.{|=|};
builtin "@eq_refl" ≔ Eq.eq_refl;
builtin "@ind_eq" ≔ Eq.ind_eq;
builtin "@neq" ≔ Eq.{|≠|};

// Bool
builtin "bool'" ≔ Bool.{|𝔹|};
builtin "bool'" ≔ Bool.bool;
builtin "is_true" ≔ Bool.istrue;
builtin "negb" ≔ Bool.not;
builtin "orb" ≔ Bool.or;
builtin "andb" ≔ Bool.and;
builtin "if'" ≔ Bool.if;

// Classic
builtin "@classic" ≔ Classic.em; 

// Comp
builtin "comparison'" ≔ Comp.comp;
builtin "comparison'" ≔ Comp.Comp;
builtin "CompOpp" ≔ Comp.opp;
builtin "isEq" ≔ Comp.isEq;
builtin "isLt" ≔ Comp.isLt;
builtin "isGT" ≔ Comp.isGt;
builtin "case_Comp" ≔ Comp.case_Comp;

// Epsilon
builtin "@eps" ≔ Epsilon.{|ε|};
builtin "@eps_spec" ≔ Epsilon.{|εᵢ|};

// Nat
builtin "nat" ≔ Nat.{|ℕ|};
builtin "O" ≔ Nat._0;
builtin "S" ≔ Nat.{|+1|};
builtin "Nat.add" ≔ Nat.{|+|};
builtin "Nat.sub" ≔ Nat.{|-|};
builtin "Nat.pred" ≔ Nat.{|∸1|};
builtin "Nat.mul" ≔ Nat.{|*|};
builtin "Nat.leb" ≔ Nat.{|≤|};
builtin "Nat.ltb" ≔ Nat.{|<|};

// List
builtin "List" ≔ List.{|𝕃|};
builtin "nil" ≔ List.{|□|};
builtin "cons" ≔ List.{|⸬|};
builtin "List.In" ≔ List.{|∈|};
builtin "app" ≔ List.{|++|};

// Pos
builtin "positive" ≔ Pos.{|ℙ|};
builtin "xI" ≔ Pos.I;
builtin "xO" ≔ Pos.O;
builtin "xH" ≔ Pos.H;
builtin "poitisve_ind" ≔ Pos.{|ind_ℙ|};

// Z
builtin "Z" ≔ Z.{|ℤ|};
builtin "Z0" ≔ Z.Z0;
builtin "Zpos" ≔ Z.Zpos;
builtin "Zneg" ≔ Z.Zneg;
builtin "Z.opp" ≔ Z.{|—|};
builtin "Z.compare" ≔ Z.{|≐|};

// DepProd
builtin "DProd" ≔ DepProd.dprod;
