import RelationalCalculus.Basic
import RelationalCalculus.Order
open Relation

namespace Relation
-- Define custom equality for Relation based on union order (inclusion)
def eq (R S : Relation α β) : Prop :=
  R ≤ S ∧ S ≤ R


-- *** Equivalence Properties ***
-- Reflexivity
@[refl]
theorem eq_refl (R : Relation α β) : eq R R :=
  ⟨le_refl R, le_refl R⟩

-- Symmetry
@[symm]
theorem eq_symm {R S : Relation α β} (h : eq R S) : eq S R :=
  ⟨h.2, h.1⟩

-- Transitivity
@[trans]
theorem eq_trans {R S T : Relation α β} (h₁ : eq R S) (h₂ : eq S T) : eq R T :=
  ⟨le_trans h₁.1 h₂.1, le_trans h₂.2 h₁.2⟩
end Relation

-- Create Setoid instance
-- A Setoid is a set together with an equivalence relation
-- After proving this instance we use ≈ for the equivalence relation between Relations
instance : Setoid (Relation α β) where
  r :=  Relation.eq
  iseqv := {
    refl := Relation.eq_refl
    symm := Relation.eq_symm
    trans := Relation.eq_trans
  }


instance : HasEquiv (Relation α β) where
Equiv := Relation.eq

-- ... and so on for other constructors

namespace Relation
-- *** Theorems Relating Order Equivalence to Evaluation Equality ***
-- Our equivalence relation defined in terms of ordering actually implies equivalence in terms of evaluation. This is because we defined ordering in terms of evaluation (see Order.lean).
theorem eq_iff_forall_eval_eq {α β : Type u} {R S : Relation α β} :
    R ≈ S ↔ (∀ a b, eval R a b ↔ eval S a b) := by
  constructor
  · intro h
    intro a b
    exact ⟨fun hr => h.1 a b hr, fun hs => h.2 a b hs⟩
  · intro h
    constructor
    · intro a b hr
      exact (h a b).1 hr
    · intro a b hs
      exact (h a b).2 hs


-- Extentional equality implies evaluation equality
theorem eq_to_eval {R S : Relation α β} (h : R ≈ S) :
    eval R = eval S := by
  funext a b
  exact propext (Relation.eq_iff_forall_eval_eq.1 h a b)

theorem eval_to_eq {R S : Relation α β} (h: eval R = eval S) : R ≈ S := by
  simp [(·≈·)]
  constructor
  · intro a b hR
    rw [←h]
    exact hR
  · intro a b hS
    rw [h]
    exact hS

theorem eq_iff_eval_eq {R S : Relation α β}: R ≈ S ↔ (eval R = eval S) := by
  exact ⟨eq_to_eval, eval_to_eq ⟩

-- TO DELETE
-- This was a much longer proof of same
-- simp [(· ≈ · ),eq, (· ≤ · )]
-- constructor
-- · intro h1
--   have RtoS := h1.1
--   have StoR := h1.2
--   have h2: ∀(a : α) (b : β), R.eval a b ↔ S.eval a b := by
--    intro a b
--    constructor
--    · exact RtoS a b
--    · exact StoR a b
--   funext a b
--   exact propext (h2 a b)
-- · intro h1
--   have h2 : ∀ a b, eval R a b ↔ eval S a b := by
--     intro a b
--     rw [h1]
--   have h3 := eq_iff_forall_eval_eq.mpr h2
--   exact h3


end Relation

def Relation.Setoid := @instSetoidRelation
def Relation.HasEquiv := @instHasEquivRelation
