import RelationalCalculus.Logic.SimpTheorems
import RelationalCalculus.Basic
import RelationalCalculus.Utility
import RelationalCalculus.Order
import RelationalCalculus.Eq
import RelationalCalculus.Union
import RelationalCalculus.Intersection
import RelationalCalculus.Residuals
import Mathlib.Tactic
import Init.SimpLemmas

open Utility
open Relation
open Logic
namespace Relation


-- To avoid name clashes we use the "R" suffix when naming logical constructs built from relational calculus expressions.
abbrev PropR :=  Relation {⋆} {⋆}
abbrev TrueR : PropR := full {⋆} {⋆}
abbrev FalseR : PropR := empty {⋆} {⋆}

theorem excludedMiddleR (R: PropR) : R ≈ TrueR ∨ R ≈ FalseR := by
simp [(·≈·), eq, TrueR, FalseR, (· ≤ ·), eval]
exact em (eval R ⋆ ⋆)

-- Note: Not sure if this is necessary.
-- theorem bivaluedProps (R S T: PropR)  : ¬(R ≈ S) → ((T ≈ R) ∨ (T ≈ S)) := by
--     intro h1
--     simp [(·≈·), eq, (·≤·),eval ]
--



-- We can prove statements in the logic of relations by showing that a propositional relation is equivalent to TrueR
def proofR (R: PropR): Prop := R ≈ TrueR

-- This simplification avoids the need to prove both directions of ≤ when proving truth equivalence
-- TODO: Finish proof
@[simp]
theorem simp_proofR_le (P: PropR) : (P ≈ TrueR) = (TrueR ≤ P)  := by
simp [(·≈·), eq, TrueR, (·≤·)]
intro _ _
simp [eval]


@[simp]
theorem simp_proofR (P: PropR) : (P ≈ TrueR) = proofR P := by
simp [proofR]


@[match_pattern]
def andR (P Q: PropR) : PropR := TrueR ▹ (copy {⋆}) ▹ P ⊗ Q ▹ merge {⋆}
infixl: 90 " ∧ " => andR

@[match_pattern]
def orR (P Q: PropR) : PropR :=  TrueR ▹ split {⋆} ▹ P ⊕ Q ▹ collapse {⋆}
infixl: 85 " ∨ " => orR

@[match_pattern]
def notR (P: PropR) : PropR := P⁻
prefix: 95 "¬" => notR -- \neg

-- This is the definition of classical implication (i.e. as opposed to linear implication ⊸)
@[match_pattern]
def impliesR (P Q: PropR) : PropR := (¬P) ∨ Q
infixr : 83 "→" => impliesR -- \imp

@[simp]
theorem simp_impliesR {P Q: PropR} : ((¬P) ∨ Q) = (P → Q) := by
simp [impliesR]

@[simp]
theorem simp_not  {P : PropR} :  P⁻ = ¬P  := by
simp [notR]


-- Turn any relation into a proposition by unit capping it with full on either side. This is the proposition that R is non-empty, which is also the existential statement that there exists some pair p ∈ R.
@[match_pattern]
def existsR (R : Relation α β) : PropR := full {⋆} α ▹ R ▹ full β {⋆}
prefix: 83 "∃" => existsR

-- TODO
theorem exists_iff_non_empty (R : Relation α β) : proofR (∃ R)  ↔ ¬(R ≈ (empty α β)) := by
  sorry


-- Uses logical equivalency of ¬∃.¬P
-- Note: To quantify over variables, we need to keep R as a geneneral relation R: α → β ; we don't propositionalize the components of R. Then this construction implicitly quantifies over α × β.
@[match_pattern]
def forAllR (R : Relation α β) := ¬existsR (R⁻)
prefix: 83 "∀" => forAllR

-- ∀ R if and only if R is equivalent the full relation.
theorem for_all_iff_full (R : Relation α β) : proofR (∀ R)  ↔  R ≈ full α β := by sorry



end Relation
