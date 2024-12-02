import RelationalCalculus.Basic
import RelationalCalculus.Order
import RelationalCalculus.Eq
import RelationalCalculus.Union
import RelationalCalculus.Intersection
import Mathlib.Tactic

open Relation
universe u
namespace Relation

def isPartialId {α :Type u} (R: Relation α α) : Prop := R ≤ (idR α)

def isEmpty {α β :Type u} (R: Relation α β) := R ≈ (empty α β)

@[simp]
theorem empty_simp {α β :Type u} {R: Relation α β } : isEmpty R = (R ≤ (empty α β)) := by simp [isEmpty, (·≤·), (·≈·), eq, eval]

def isNonEmpty {α β :Type u} (R: Relation α β ) : Prop := ¬ isEmpty R
-- Define an element relation

def isMinimal {α β :Type u} (R: Relation α β ) : Prop := R ≈ (R▹(full β α)▹R)

-- Element relation defined compositionally
def isElement {α :Type u}  (R: Relation α α) : Prop := isPartialId R ∧ isNonEmpty R ∧ isMinimal R

-- An element relation is equivalent to a reflexive pair (a,a)
theorem element_imp_refl_pair {α : Type u} (R : Relation α α) :
  (isElement R) →  (∃ (a : α), (R ≈ pair a a)) := by
  simp [isElement, (·≈·), eq, (·≤·), isPartialId, isNonEmpty, isMinimal, eval, domain, codomain]
  -- Forward direction
  intro h_id x x₁ nonempty minimal1 minimal2
  have minimal  : ∀ (a b y : α), R.eval a y → ∀ (x : α), R.eval x b → R.eval a b := by exact minimal2
  -- In words: If a is connected to anything y, and anything x is connected to b, then a is connected to b. This the useful bit, minimal1 is trivial.
  have xEqx₁ : x = x₁ := h_id x x₁ nonempty
  let a := x
  have aRa : R.eval a a := by rwa [← xEqx₁] at nonempty
  -- We will show that R.eval a₁ b → a₁ = a ∧ b = a
  have h_unique : ∀ (a₁ b₁ : α), R.eval a₁ b₁ → (a =  a₁) ∧ (a = b₁) := by
    intros a₁ b₁ a₁Rb₁
    have a₁Eqb₁ : a₁ = b₁ := h_id a₁ b₁ a₁Rb₁
    have aRb₁ :=  minimal a b₁ a aRa a₁ a₁Rb₁
    have aRa₁ : R.eval a a₁ := by rwa [a₁Eqb₁.symm] at aRb₁
    have a₁Eqa  :=  ((h_id a a₁) aRa₁).symm
    have b₁Eqa : b₁ = a := by rwa [← a₁Eqb₁]
    exact ⟨a₁Eqa.symm, b₁Eqa.symm⟩
  use a


-- If a relation is equivalent to a reflexive pair, it is an element relation.
theorem refl_pair_imp_element {α : Type u} (R : Relation α α) :
  (∃ (a : α), (R ≈ pair a a)) →  (isElement R)  := by
  simp [isElement, (·≈·), eq, (·≤·), isPartialId, isNonEmpty, isMinimal, eval, domain, codomain]
  intro a unique aRa

  have partial_id : ∀ (a₁ b : α), R.eval a₁ b → a₁ = b := by
    intros a₁ b h_eval
    specialize unique a₁ b h_eval
    rw [unique.1.symm]
    exact unique.2

  have nonempty : ∃ x x₁, R.eval x x₁ := ⟨a, a, aRa⟩

  -- Prove R ≈ R ▹ full α α ▹ R (minimality)
  have minimal : isMinimal R  := by
    simp [isElement, (·≈·), eq, (·≤·), isPartialId, isNonEmpty, isMinimal, eval, domain, codomain]
    constructor
    · intro a₁ b a₁Rb
      constructor
      · use b
      · use a₁
    · intro a₁ b y a₁Ry x xRb
      have a₁_a : a₁ = a  := (unique a₁ y a₁Ry).1.symm
      have b_a : b = a := (unique x b xRb).2.symm
      rwa [a₁_a, b_a]

  simp [isElement, (·≈·), eq, (·≤·), isPartialId, isNonEmpty, isMinimal, eval, domain, codomain] at minimal
  exact ⟨partial_id, nonempty, minimal  ⟩
