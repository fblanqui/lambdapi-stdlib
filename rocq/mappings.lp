// ---------------------------------------------------------------------------
// Core correspondence mappings
// ---------------------------------------------------------------------------
// These establish the intended direct encoding from Lambdapi/STT symbols to
// native Rocq symbols. 

// Prop.lp
builtin "Prop" ≔ Prop;
builtin "True" ≔ {|⊤|};
builtin "I" ≔ {|⊤ᵢ|};
builtin "False" ≔ {|⊥|};
builtin "@False_ind" ≔ {|⊥ₑ|};
builtin "imp" ≔ {|⇒|};
builtin "not" ≔ {|¬|};
builtin "and" ≔ {|∧|};
builtin "@conj" ≔ {|∧ᵢ|};
builtin "@proj1" ≔ {|∧ₑ₁|};
builtin "@proj2" ≔ {|∧ₑ₂|};
builtin "\/" ≔ {|∨|};
builtin "@or_introl" ≔ {|∨ᵢ₁|};
builtin "@or_intror" ≔ {|∨ᵢ₂|};
builtin "or_elim" ≔ {|∨ₑ|};
builtin "@ex_intro" ≔ {|∃ᵢ|};
builtin "ex_elim" ≔ {|∃ₑ|};
builtin "iff" ≔ {|⇔|};

// Set.lp
builtin "Type'" ≔ Set;
builtin "nat" ≔ {|ι|};
builtin "el" ≔ el;

// FOL.lp
builtin "@all" ≔ {|∀|};
builtin "ex_" ≔ {|∃|};

// HOL.lp
builtin "arr" ≔ {|⤳|};

// Impred.lp
builtin "o" ≔ o;

// Eq.lp
builtin "eq" ≔ {|=|};
builtin "@eq_refl" ≔ eq_refl;
builtin "@ind_eq" ≔ ind_eq;
builtin "@neq" ≔ {|≠|};

// Bool.lp core
builtin "bool'" ≔ {|𝔹|};
builtin "bool'" ≔ bool;
builtin "true" ≔ true;
builtin "false" ≔ false;
builtin "@bool_rect" ≔ {|ind_𝔹|};
builtin "Is_true" ≔ istrue;
builtin "negb" ≔ not;
builtin "orb" ≔ or;
builtin "andb" ≔ and;
builtin "if'" ≔ if;

// Nat.lp core
builtin "nat" ≔ {|ℕ|};
builtin "O" ≔ _0;
builtin "S" ≔ {|+1|};
builtin "nat_ind" ≔ {|ind_ℕ|};
builtin "nat'" ≔ nat;
builtin "is0" ≔ is0;
builtin "pred" ≔ {|∸1|};
builtin "Nat.eqb" ≔ eqn;
builtin "eqn_correct" ≔ eqn_correct;
builtin "eqn_complete" ≔ eqn_complete;
builtin "eqn_refl" ≔ eqn_refl;
builtin "eqn_sym" ≔ eqn_sym;
builtin "Nat.add" ≔ {|+|};
builtin "Nat.sub" ≔ {|-|};
builtin "Nat.mul" ≔ {|*|};
builtin "leq" ≔ {|≤|};
builtin "ltn" ≔ {|<|};
builtin "geq" ≔ {|≥|};
builtin "gtn" ≔ {|>|};
builtin "maxn" ≔ max;
builtin "minn" ≔ min;
builtin "expn" ≔ {|^|};
builtin "factn" ≔ !;

// List.lp core used by Disj.lp
builtin "list" ≔ list_type;
builtin "lp_u1d543" ≔ {|𝕃|};
builtin "lp_u25a1" ≔ {|□|};
builtin "lp_u2e2c" ≔ {|⸬|};
builtin "lp_ind_u1d543" ≔ {|ind_𝕃|};
builtin "lp_u2208" ≔ {|∈|};
builtin "lp_u2286" ≔ {|⊆|};
builtin "lp_u002b_u002b" ≔ {|++|};
builtin "nth" ≔ lp_nth;
builtin "nths" ≔ nths;
builtin "size" ≔ size;
builtin "iota" ≔ iota;
builtin "indexes" ≔ indexes;
builtin "indexes_decrement" ≔ indexes_decrement;
builtin "rem_nth" ≔ rem_nth;
builtin "set_nth" ≔ set_nth;
builtin "undup_first" ≔ undup_first;

// Disj.lp/Conj.lp shim
builtin "disj" ≔ disj;
builtin "preserves_contents" ≔ preserves_contents;
builtin "conj" ≔ conj_list;
builtin "insertBot" ≔ insertBot;
builtin "insertBots" ≔ insertBots;

// Classic.lp
builtin "classic" ≔ em; 

// Comp.lp core
builtin "comparison'" ≔ comp;
builtin "comparison'" ≔ Comp;
builtin "Eq" ≔ Eq;
builtin "Lt" ≔ Lt;
builtin "Gt" ≔ Gt;
builtin "ind_Comp" ≔ ind_Comp;
builtin "CompOpp" ≔ opp;
builtin "isEq" ≔ isEq;
builtin "isLt" ≔ isLt;
builtin "isGt" ≔ isGt;
builtin "isLe" ≔ isLe;
builtin "isGe" ≔ isGe;
builtin "case_Comp" ≔ case_Comp;

// Epsilon.lp
builtin "eps" ≔  {|ε|};
builtin "eps_spec" ≔  {|εᵢ|};

// ---------------------------------------------------------------------------
// Stdlib shim workaround mappings
// ---------------------------------------------------------------------------
// These replace selected Lambdapi/Dedukti stdlib declarations or theorem
// proofs whose original behavior depends on rewrite rules that Rocq does not
// see as definitional computation.

// Bool.lp shim
builtin "case_𝔹" ≔ {|case_𝔹|};
builtin "ind_𝔹_eq" ≔ {|ind_𝔹_eq|};
builtin "istrue_eq_true" ≔ {|istrue=true|};
builtin "true_eq_istrue" ≔ {|true=istrue|};
builtin "not_istrue_eq_false" ≔ {|¬istrue=false|};
builtin "false_eq_not_istrue" ≔ {|false=¬istrue|};
builtin "false_neq_true" ≔ {|false≠true|};
builtin "true_neq_false" ≔ {|true≠false|};
builtin "not_istrue" ≔ {|¬_istrue|};
builtin "bool_istrue_not" ≔ istrue_not;
builtin "or_istrue" ≔ {|∨_istrue|};
builtin "bool_istrue_or" ≔ istrue_or;
builtin "or_i1" ≔ {|orᵢ₁|};
builtin "or_i2" ≔ {|orᵢ₂|};
builtin "or_e" ≔ {|orₑ|};
builtin "orC" ≔ orC;
builtin "orA" ≔ orA;
builtin "and_istrue" ≔ {|∧_istrue|};
builtin "bool_istrue_and" ≔ istrue_and;
builtin "and_i" ≔ {|andᵢ|};
builtin "and_e1" ≔ {|andₑ₁|};
builtin "and_e2" ≔ {|andₑ₂|};

// Nat.lp shim
builtin "Nat.add_1_r" ≔ addn1;
builtin "addSnnS" ≔ addSnnS;
builtin "Nat.add_comm" ≔ addnC;
builtin "addnA" ≔ addnA;
builtin "addnCA" ≔ addnCA;
builtin "addnAC" ≔ addnAC;
builtin "addnCAC" ≔ addnCAC;
builtin "addnACl" ≔ addnACl;
builtin "addnACA" ≔ addnACA;
builtin "addnI" ≔ addnI;
builtin "addIn" ≔ addIn;
builtin "lp_2_u002a_u003d_0" ≔ {|2*=0|};
builtin "lp_2_u002a_inj" ≔ {|2*_inj|};
builtin "lp_odd_u2260_even" ≔ {|odd≠even|};
builtin "sub0n" ≔ sub0n;
builtin "subn1" ≔ subn1;
builtin "subnn" ≔ subnn;
builtin "subnS" ≔ subnS;
builtin "predn_sub" ≔ predn_sub;
builtin "subnAC" ≔ subnAC;
builtin "addnK" ≔ addnK;
builtin "subnDA" ≔ subnDA;
builtin "subnDl" ≔ subnDl;
builtin "mul0n" ≔ mul0n;
builtin "muln0" ≔ muln0;
builtin "mul1n" ≔ mul1n;
builtin "muln1" ≔ muln1;
builtin "mulSn" ≔ mulSn;
builtin "mulSnr" ≔ mulSnr;
builtin "mulnS" ≔ mulnS;
builtin "mulnSr" ≔ mulnSr;
builtin "mulnC" ≔ mulnC;
builtin "mulnDl" ≔ mulnDl;
builtin "mulnDr" ≔ mulnDr;
builtin "mulnBr" ≔ mulnBr;
builtin "mulnBl" ≔ mulnBl;
builtin "mulnA" ≔ mulnA;
builtin "mulnCA" ≔ mulnCA;
builtin "mulnAC" ≔ mulnAC;
builtin "mulnACA" ≔ mulnACA;
builtin "muln_eq0" ≔ muln_eq0;
builtin "lp_u2264_0" ≔ {|≤0|};
builtin "lp_u2264_refl" ≔ {|≤_refl|};
builtin "eq_leq" ≔ eq_leq;
builtin "leq_trans" ≔ leq_trans;
builtin "eqn_leq" ≔ eqn_leq;
builtin "leqsnn" ≔ leqsnn;
builtin "letnS" ≔ letnS;
builtin "ltn0" ≔ ltn0;
builtin "ltnn" ≔ ltnn;
builtin "ltnSn" ≔ ltnSn;
builtin "leq0n" ≔ leq0n;
builtin "ltn0Sn" ≔ ltn0Sn;
builtin "leqnSn" ≔ leqnSn;
builtin "leq_pred" ≔ leq_pred;
builtin "ltnW" ≔ ltnW;
builtin "leqW" ≔ leqW;
builtin "ltn_trans" ≔ ltn_trans;
builtin "lp_u003c_asym" ≔ {|<_asym|};
builtin "anti_ltn" ≔ anti_ltn;
builtin "leq_total" ≔ leq_total;
builtin "lt0n" ≔ lt0n;
builtin "leq_eqVlt" ≔ leq_eqVlt;
builtin "leq_add0" ≔ leq_add0;
builtin "leq_add2l" ≔ leq_add2l;
builtin "ltn_add2l" ≔ ltn_add2l;
builtin "leq_add2r" ≔ leq_add2r;
builtin "ltn_add2r" ≔ ltn_add2r;
builtin "leq_addl" ≔ leq_addl;
builtin "leq_addr" ≔ leq_addr;
builtin "leq_subr" ≔ leq_subr;
builtin "subn_eq0" ≔ subn_eq0;
builtin "ltn_addl" ≔ ltn_addl;
builtin "ltn_addr" ≔ ltn_addr;
builtin "addn_gt0" ≔ addn_gt0;
builtin "subn_gt0" ≔ subn_gt0;
builtin "leq_add" ≔ leq_add;
builtin "leq_subLR" ≔ leq_subLR;
builtin "subnKC" ≔ subnKC;
builtin "addnBn" ≔ addnBn;
builtin "addnBA" ≔ addnBA;
builtin "subnK" ≔ subnK;
builtin "subSn" ≔ subSn;
builtin "addnBAC" ≔ addnBAC;
builtin "leq_sub2r" ≔ leq_sub2r;
builtin "leq_sub2l" ≔ leq_sub2l;
builtin "leq_sub" ≔ leq_sub;
builtin "maxnC" ≔ maxnC;
builtin "maxnA" ≔ maxnA;
builtin "maxnAC" ≔ maxnAC;
builtin "maxnCA" ≔ maxnCA;
builtin "maxnACA" ≔ maxnACA;
builtin "addn_maxl" ≔ addn_maxl;
builtin "addn_maxr" ≔ addn_maxr;
builtin "subn_maxl" ≔ subn_maxl;
builtin "maxnE" ≔ maxnE;
builtin "maxnn" ≔ maxnn;
builtin "leq_pmull" ≔ leq_pmull;
builtin "leq_pmulr" ≔ leq_pmulr;
builtin "leq_mul2l" ≔ leq_mul2l;
builtin "leq_mul2r" ≔ leq_mul2r;
builtin "leq_mul" ≔ leq_mul;
builtin "eqn_mul2l" ≔ eqn_mul2l;
builtin "eqn_mul2r" ≔ eqn_mul2r;
builtin "leq_pmul2l" ≔ leq_pmul2l;
builtin "leq_pmul2r" ≔ leq_pmul2r;
