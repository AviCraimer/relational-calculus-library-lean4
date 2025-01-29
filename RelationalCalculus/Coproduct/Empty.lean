import RelationalCalculus.Basic
import RelationalCalculus.Order
import RelationalCalculus.Eq
import RelationalCalculus.Element
import RelationalCalculus.Empty
import Mathlib.Tactic

namespace Relation
open Relation

-- If the left side of a coproduct is not empty, then the coproduct is not empty
-- note the contrapositive of this is:
  --  ((T⊕U) ≈ empty (Sum α δ) (Sum β γ)) → (T ≈ empty α β)
lemma coprod_empty_cong_left {α β δ γ  :Type u} (T: Relation α β)(U: Relation δ γ) : ¬(T ≈ empty α β) → ¬( (T⊕U) ≈ empty (Sum α δ) (Sum β γ)) := by
  simp
  have h1 := not_false_exists_pair T.eval
  have h2 :=  not_false_exists_pair (T ⊕ U).eval
  rw [h1, h2]
  intro ETab
  simp at ETab
  simp [eval]
  constructor
  · exact ETab

-- Same as above but for the right side.
lemma coprod_empty_cong_right {α β δ γ  :Type u} (T: Relation α β)(U: Relation δ γ) : ¬(U ≈ empty δ γ) → ¬( (T⊕U) ≈ empty (Sum α δ) (Sum β γ)) := by
  simp
  have h1 := not_false_exists_pair U.eval
  have h2 :=  not_false_exists_pair (T ⊕ U).eval
  rw [h1, h2]
  intro EUab
  simp at EUab
  simp [eval]
  simp_all only [or_true]


-- The emptiness of a coproduct is congruenent with the conjunction of emptiness of its components.
theorem coprod_empty_cong {α β δ γ  :Type u} (T: Relation α β)(U: Relation δ γ) : ( (T⊕U) ≈ empty (Sum α δ) (Sum β γ)) = ((T ≈ empty α β) ∧ (U ≈ empty δ γ)) :=  by
  have left := coprod_empty_cong_left T U
  have right := coprod_empty_cong_right T U
  simp only [eq_iff_iff]
  constructor
  · intro a
    simp_all only [equiv_eq_eval, empty_eval_false, not_true_eq_false, imp_false, not_not, and_self]
  · intro ⟨Tempty, Uempty⟩
    by_contra cn
    simp at cn
    rw [not_false_exists_pair (T ⊕ U).eval] at cn
    simp_all
    cases cn with
    | inl h =>
      obtain ⟨w, h⟩ := h
      cases h with
      | inl h_1 =>
        obtain ⟨w_1, h⟩ := h_1
        simp [eval] at h
        simp_all
      | inr h_2 =>
        obtain ⟨_, h⟩ := h_2
        exact h
    | inr h_1 =>
      obtain ⟨w, h⟩ := h_1
      cases h with
      | inl h_1 =>
        obtain ⟨_, h⟩ := h_1
        exact h
      | inr h_2 =>
        obtain ⟨w_1, h⟩ := h_2
        simp [eval] at h
        simp_all
