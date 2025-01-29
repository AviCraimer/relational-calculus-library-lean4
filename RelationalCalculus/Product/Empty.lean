import RelationalCalculus.Basic
import RelationalCalculus.Order
import RelationalCalculus.Eq
import RelationalCalculus.Element
import RelationalCalculus.Empty
import Mathlib.Tactic

namespace Relation
open Relation

-- If the left side of a product is empty, then the product is empty
lemma prod_empty_cong_left {α β δ γ  :Type u} (T: Relation α β)(U: Relation δ γ) : (T ≈ empty α β) → ( (T⊗U) ≈ empty (α × δ) (β × γ)) := by
  simp
  simp [eval]
  intro TFalse
  simp_all only [false_and]

-- Contrapositive
theorem prod_not_empty_left {α β δ γ  :Type u} (T: Relation α β)(U: Relation δ γ) : ¬T ⊗ U ≈ empty (α × δ) (β × γ) → ¬T ≈ empty α β := not_imp_not.mpr (prod_empty_cong_left
T U)

lemma prod_empty_cong_right {α β δ γ  :Type u} (T: Relation α β)(U: Relation δ γ) : (U ≈ empty δ γ) → ( (T⊗U) ≈ empty (α × δ) (β × γ)) := by
  simp
  simp [eval]
  intro UFalse
  simp_all only [and_false]

-- Contrapositive
theorem prod_not_empty_right {α β δ γ  :Type u} (T: Relation α β)(U: Relation δ γ) : ¬T ⊗ U ≈ empty (α × δ) (β × γ) → ¬U ≈ empty δ γ := not_imp_not.mpr (prod_empty_cong_right
T U)

-- The emptiness of a product is congruenent with the logical disjunction of the emptiness of its components.
theorem prod_empty_cong {α β δ γ  :Type u} (T: Relation α β)(U: Relation δ γ) : ( (T⊗U) ≈ empty (α × δ) (β × γ)) = ((T ≈ empty α β) ∨ (U ≈ empty δ γ)) :=  by
simp
have h1 := not_false_exists_pair (T ⊗ U).eval
constructor <;> intro h
· contrapose! h
  obtain ⟨nTEmpty, nUEmpty⟩ := h
  simp_all only [eq_iff_iff, iff_true, Prod.exists, ne_eq]
  simp [eval]
  constructor
  · rw [not_false_exists_pair T.eval] at nTEmpty
    simp_all only [eq_iff_iff, iff_true]
  · rw [not_false_exists_pair U.eval] at nUEmpty
    simp_all only [eq_iff_iff, iff_true]
· by_contra cn
  rw [empty_eval_false.symm] at cn
  have h2 : ¬T ⊗ U ≈ empty (α × δ) (β × γ) := by simp_all only [eq_iff_iff, iff_true, Prod.exists,
    empty_eval_false, equiv_eq_eval]
  have h3 := (prod_not_empty_left T U) h2
  have h4 := (prod_not_empty_right T U) h2
  simp_all only [eq_iff_iff, iff_true, Prod.exists, empty_eval_false, equiv_eq_eval, or_self]
