// Prop
builtin "Prop" ≔ Prop;
builtin "True" ≔ ⊤;
builtin "I" ≔ ⊤ᵢ;
builtin "False" ≔ ⊥;
builtin "False_ind" ≔ ⊥ₑ;
builtin "imp" ≔ ⇒;
builtin "not" ≔ ¬;
builtin "and" ≔ ∧;
builtin "conj" ≔ ∧ᵢ;
builtin "proj1" ≔ ∧ₑ₁;
builtin "proj2" ≔ ∧ₑ₂;
builtin "\/" ≔ ∨;
builtin "or_intro1" ≔ ∨ᵢ₁;
builtin "or_intro2" ≔ ∨ᵢ₂;
builtin "or_elim" ≔ ∨ₑ;
builtin "ex_intro" ≔ ∃ᵢ;
builtin "ex_elim" ≔ ∃ₑ;
builtin "iff" ≔ ⇔;

// Set
builtin "Type'" ≔ Set;
builtin "nat" ≔ ι;
builtin "el" ≔ el;

// Prod
builtin "prod" ≔ ×;

// FOL
builtin "all" ≔ ∀;
builtin "ex" ≔ ∃;

// HOL
builtin "arr" ≔ ⤳;

// Eq
builtin "eq" ≔ =;
builtin "eq_refl" ≔ eq_refl;
builtin "ind_eq" ≔ ind_eq;
builtin "neq" ≔ ≠;

// Bool
builtin "bool'" ≔ 𝔹;
builtin "bool'" ≔ bool;
builtin "Is_true" ≔ istrue;
builtin "negb" ≔ not;
builtin "orb" ≔ or;
builtin "andb" ≔ and;
builtin "if'" ≔ if;

// Classic
builtin "classic" ≔ em; 

// Comp
builtin "comparison'" ≔ comp;
builtin "comparison'" ≔ Comp;
builtin "CompOpp" ≔ opp;
builtin "isEq" ≔ isEq;
builtin "isLt" ≔ isLt;
builtin "isGT" ≔ isGT;
builtin "case_Comp" ≔ case_Comp;

// Epsilon
builtin "eps" ≔  ε;
builtin "eps_spec" ≔  εᵢ;

// Nat
builtin "nat" ≔ ℕ;

// List
builtin "List" ≔ 𝕃;
builtin "nil" ≔ □;
builtin "cons" ≔ ⸬;
builtin "List.In" ≔ ∈;
builtin "app" ≔ ++;
