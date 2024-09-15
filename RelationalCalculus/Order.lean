import RelationalCalculus.Basic
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
-- This automatically enables us to use ≤ notation to indicate ordering of relations. Note that the use of ≤ is essentially a semantic operation since it is defined in terms of evaluation. Later we'll see that linear implication (⊸) give as an equivalent algebraic definition of subrelations with the relation R ⊸ S corresponding to the semantics S ≤ R.
-- Since turning R ⊸ S into a statement about ording requires defining propositions as relations, we get to this in Logic.lean.

instance : Preorder (Relation α β) where
  le := (· ≤ ·)
  le_refl := Relation.le_refl
  le_trans := @Relation.le_trans _ _



def Relation.Preorder := @instPreorderRelation

def Relation.le {α β : Type u} := (@instLERelation α β).le
