// symbols used for encoding simple type theory

builtin "Set" ≔ Sort.Set;
builtin "El" ≔ Sort.{|τ|};
builtin "arr" ≔ Sort.{|⤳|};
builtin "prop" ≔ Prop.Prop;
builtin "Prf" ≔ Prop.{|π|};
builtin "imp" ≔ Prop.{|⇒|};
builtin "not" ≔ Prop.{|¬|};
builtin "or" ≔ Prop.{|∨|};
builtin "and" ≔ Prop.{|∧|};
builtin "eq" ≔ Eq.=;
builtin "all" ≔ FOL.{|∀|};
builtin "ex" ≔ FOL.{|∃|};
