
import RelationalCalculus.Basic
import RelationalCalculus.Order
import RelationalCalculus.Eq
import Mathlib.Tactic
open Relation


--- *** Relational Union ***

-- Compositional definition of union of relations. I should prove that this yeilds the set theoretic definition of union of pairs.
@[match_pattern]
def Relation.union (R : Relation α β) (S : Relation α β) := comp (comp (Relation.split α) (coproduct R S)) (collapse β)

namespace Relation
infixl:50 "∪" => Relation.union
end Relation

-- We give the direct set-theoretic definition of a union of two relations.
def Relation.union_pairs_def (R : Relation α β) (S : Relation α β) : Pairs α β  := fun a b => (eval R) a b ∨ (eval S) a b

-- Proof that the compositional definition of union is equal to the set theoretic definiton.
theorem Relation.union_eval_eq_pairs (R : Relation α β) (S : Relation α β) : eval (Relation.union R S) = union_pairs_def R S := by
apply funext
intro a
apply funext
intro b
simp [Relation.eval, union_pairs_def, Relation.union]

theorem Relation.union_assoc {R S T : Relation α β} :
     ((R ∪ S) ∪ T) ≈ (R ∪ (S ∪ T)) := by
rw [eq_iff_forall_eval_eq]
simp [union, (·≈·), eval]
intro a b
have assoc :=  @or_assoc (R.eval a b) (S.eval a b) (T.eval a b)
constructor <;> intro h1
· exact assoc.mp  h1
· exact assoc.mpr h1

-- A left side of a union is less then or equal to the union it is a part of
theorem Relation.union_left_le  (R S : Relation α β) : R ≤ Relation.union R S := by
  intros a b h
  simp [union, eval]
  use Or.inl h

-- -- A right side of a union is less then or equal to the union it is a part of
theorem Relation.union_right_le   (R S : Relation α β) : R ≤ Relation.union S R := by
  intros a b h
  simp [union, eval]
  use Or.inr h

-- Union of two lesser relations is lesser, i.e., union preserves ordering
theorem Relation.union_le {R S T : Relation α β} (hR : R ≤ T) (hS : S ≤ T) : Relation.union R S ≤ T := by
  intros a b h
  simp [Relation.eval, Relation.union] at h
  rcases h with aRb | aSb
  · exact hR a b aRb
  · exact hS a b aSb


-- Proof that union is commutative.
theorem Relation.union_comm  {α β : Type u } {R S : Relation α β } : (S ∪ R) ≈ (R ∪ S) := by
simp [(·≈·)]
have RLeft :  R ≤ (R ∪ S) := union_left_le R S
have RRight :  R ≤ (S ∪ R) := union_right_le R S
have SLeft :  S ≤ (S ∪ R) := union_left_le S R
have SRight :  S ≤ (R ∪ S) := union_right_le S R
have SR_le_RS := union_le  SRight RLeft
have RS_le_SE := union_le RRight SLeft
exact ⟨SR_le_RS, RS_le_SE⟩
