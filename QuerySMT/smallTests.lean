import QuerySMT
import Aesop
import Mathlib.Tactic.Linarith

set_option auto.smt true
set_option auto.smt.solver.name "cvc5"
set_option auto.smt.dumpHints true

set_option auto.smt.save false
set_option auto.smt.savepath "/Users/joshClune/Desktop/temp.smt"

set_option trace.duper.ignoredUnusableFacts true

set_option linter.deprecated true

set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true
set_option trace.auto.smt.proof true
set_option trace.auto.smt.parseTermErrors true

set_option trace.querySMT.debug true
set_option duper.throwPortfolioErrors false

set_option duper.collectDatatypes true
set_option auto.getHints.failOnParseError true

-- set_option querySMT.filterHints false

example (x y z : Int) : x ≤ y → y ≤ z → x ≤ z := by
  querySMT

example (f : Int → Int) (h1 : ∀ x y, f x = f y → x = y)
(h2 : ∃ x, ∀ y, f x ≤ f y) : ∃ x, ∀ y, x ≠ y → f x < f y := by
  apply @Classical.byContradiction
  intro negGoal
  skolemizeAll
  have smtLemma0 : (∀ (_i_0 : ℤ), f sk0 ≤ f _i_0) → ∀ (_i_0 : ℤ), ¬f sk0 + -Int.ofNat 1 * f _i_0 ≥ Int.ofNat 1 := by
    grind
  have smtLemma1 :
    (∀ (_i : ℤ),
        have _let_1 := sk1 _i;
        ¬(¬_i = _let_1 → f _i < f _let_1)) →
      ∀ (bv1 : ℤ), f bv1 + -Int.ofNat 1 * f (sk1 bv1) ≥ Int.ofNat 0 :=
    by grind
  have smtLemma2 :
    have _let_1 := f (sk1 sk0);
    have _let_2 := f sk0;
    have _let_3 := _let_2 + -Int.ofNat 1 * _let_1;
    (¬_let_3 ≥ Int.ofNat 0 ∨ _let_2 = _let_1) ∨ _let_3 ≥ Int.ofNat 1 :=
    by grind
  duper [h1, h2, negGoal, smtLemma0, smtLemma1, smtLemma2] []
  -- OLD OUTPUT
  -- apply @Classical.byContradiction
  -- intro negGoal
  -- skolemizeAll
  -- have smtLemma0 : (∀ (_i_0 : ℤ), f sk0 ≤ f _i_0) → ∀ (_i_0 : ℤ), ¬f sk0 + -Int.ofNat 1 * f _i_0 ≥ Int.ofNat 1 := by
  --   grind
  -- have smtLemma1 :
  --   (∀ (_i : ℤ),
  --       have _let_1 := sk1 _i;
  --       ¬(¬_i = _let_1 → f _i < f _let_1)) →
  --     ∀ (BOUND_VARIABLE_4962 : ℤ), f BOUND_VARIABLE_4962 + -Int.ofNat 1 * f (sk1 BOUND_VARIABLE_4962) ≥ Int.ofNat 0 :=
  --   by grind
  -- have smtLemma2 :
  --   have _let_1 := f (sk1 sk0);
  --   have _let_2 := f sk0;
  --   have _let_3 := _let_2 + -Int.ofNat 1 * _let_1;
  --   (¬_let_3 ≥ Int.ofNat 0 ∨ _let_2 = _let_1) ∨ _let_3 ≥ Int.ofNat 1 :=
  --   by grind
  -- duper [h1, h2, negGoal, smtLemma0, smtLemma1, smtLemma2] []

example (f : Int → Int) (h1 : ∀ x y, f x = f y → x = y)
(h2 : ∃ x, ∀ y, f x ≤ f y) : ∃ x, ∀ y, x ≠ y → f x < f y := by
  apply @Classical.byContradiction
  intro negGoal
  skolemizeAll
  have smtLemma0 : (∀ (_i_0 : Int), f sk0 ≤ f _i_0) →
    ∀ (_i_0 : Int), ¬f sk0 + -Int.ofNat 1 * f _i_0 ≥ Int.ofNat 1 :=
    by grind
  have smtLemma1 :
    (∀ (_i : Int),
        have _let_1 := sk1 _i;
        ¬(¬_i = _let_1 → f _i < f _let_1)) →
      ∀ (BOUND_VARIABLE_4962 : Int), f BOUND_VARIABLE_4962 +
    -Int.ofNat 1 * f (sk1 BOUND_VARIABLE_4962) ≥ Int.ofNat 0 :=
    by grind
  have smtLemma2 :
    have _let_1 := f (sk1 sk0);
    have _let_2 := f sk0;
    have _let_3 := _let_2 + -Int.ofNat 1 * _let_1;
    (¬_let_3 ≥ Int.ofNat 0 ∨ _let_2 = _let_1) ∨
    _let_3 ≥ Int.ofNat 1 := by grind
  duper [h1, h2, negGoal, smtLemma0, smtLemma1, smtLemma2] []

example (f : Int → Int) (h1 : ∀ x y, f x = f y → x = y)
  (h2 : ∃ x, ∀ y, f x ≤ f y) : ∃ x, ∀ y, x ≠ y → f x < f y := by
  apply @Classical.byContradiction
  intro negGoal
  skolemizeAll
  have smtLemma0 : ∀ (_i_0 : Int), ¬f sk0 - f _i_0 ≥ 1 := by grind
  have smtLemma1 : ∀ (z : Int), f z - f (sk1 z) ≥ 0 := by grind
  have smtLemma2 :
    (¬f sk0 - f (sk1 sk0) ≥ 0 ∨ f sk0 = f (sk1 sk0)) ∨
    f sk0 - f (sk1 sk0) ≥ 1 := by grind
  duper [h1, h2, negGoal, smtLemma0, smtLemma1, smtLemma2] []

-- first step, replace bound variables with reasonable names
