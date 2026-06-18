// Classic
builtin "not_not_elim" ≔ {|¬¬ₑ|};
builtin "or_not_intro" ≔ {|∨¬ᵢ|};
builtin "ex_not_intro" ≔ {|∃¬ᵢ|};

// Bool
builtin "ind_bool" ≔ {|ind_𝔹|};
builtin "case_bool" ≔ {|case_𝔹|};
builtin "ind_bool_eq" ≔ {|ind_𝔹_eq|};

// Nat
builtin "geb" ≔ {|≥|};
builtin "gtb" ≔ >;
builtin "exp" ≔ ^;
builtin "factorial" ≔ !;

// List
builtin "In_nat" ≔ {|∈ₙ|};
builtin "is_nil" ≔ {|is□|};
builtin "incl" ≔ {|⊆|};
builtin "incl_nat" ≔ {|⊆ₙ|};
