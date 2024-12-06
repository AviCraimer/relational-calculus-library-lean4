import RelationalCalculus.Basic
import Mathlib.Tactic
open Relation

-- Ordering by Inclusion
-- Define the LE instance for Relation
-- Now we can use ≤ notation for relations

 instance : LE (Relation α β) where
    le R S := ∀ a b, eval R a b → eval S a b

namespace Relation
--  R ≤  S if and only if they eval to pair functions that are less than or equal to eachother.

theorem le_rel_iff_le_eval {α β : Type u} {R S : Relation α β} :
    R ≤ S ↔ (eval R ≤ eval S) := by
  rfl

-- Prove that this ordering is reflexive
theorem le_refl (R : Relation α β) : R ≤ R := by
  intros _ _ h
  exact h

-- Prove that this ordering is transitive
theorem le_trans {R S T : Relation α β} (h₁ : R ≤ S) (h₂ : S ≤ T) : R ≤ T := by
  intros a b hR
  exact h₂ a b (h₁ a b hR)

end Relation


-- Create the Preorder instance
-- This automatically enables us to use ≤ notation to indicate ordering of relations. Note that the use of ≤ is essentially a semantic operation since it is defined in terms of evaluation.
instance : Preorder (Relation α β) where
  le := (· ≤ ·)
  le_refl := Relation.le_refl
  le_trans := @Relation.le_trans _ _

@[simp]
def le_notation_simp {α β : Type u} {R S: Relation α β }  : (R ≤ S) = ∀ (a : α) (b : β), R.eval a b → S.eval a b:= by rfl


def Relation.Preorder := @instPreorderRelation

def Relation.le {α β : Type u} := (@instLERelation α β).le


--- ORDER THEOREMS ---


-- Left monotonicity: if S ≤ T then (R▹S) ≤ (R▹T)
theorem comp_monotonic_left {α β γ: Type u} (R: Relation α β) (S T: Relation β γ)
    (h: S ≤ T): (R▹S) ≤ (R▹T) := by
  simp [(·≤·), eval, domain, codomain]
  intro a c b Rab Sbc
  use b
  constructor
  · exact Rab
  · apply h
    simp_all

-- Right monotonicity: if S ≤ T then (S▹R) ≤ (T▹R)
theorem comp_monotonic_right {α β γ: Type u} (S T: Relation α β) (R: Relation β γ)
    (h: S ≤ T): (S▹R) ≤ (T▹R) := by
  simp [(·≤·), eval, domain, codomain]
  intro a c b Sab Rbc
  use b
  constructor
  · apply h
    simp_all
  · exact Rbc


-- Monotonicity for relative sum
theorem sum_monotonic_left {α β γ: Type u} (R: Relation α β) (S T: Relation β γ) (h: S ≤ T): (R✦S) ≤ (R✦T) := by
  simp_all [eval]


theorem sum_monotonic_right {α β γ: Type u} (S T: Relation α β) (R: Relation β γ) (h: S ≤ T): (S✦R) ≤ (T✦R) := by
  simp_all [eval]
  intro a c nS_R b nT
  apply nS_R
  apply Aesop.BuiltinRules.not_intro
  intro Sab
  simp_all only [not_true_eq_false]
