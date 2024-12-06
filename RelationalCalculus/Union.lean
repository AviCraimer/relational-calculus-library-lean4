import RelationalCalculus.Basic
import RelationalCalculus.Order
import RelationalCalculus.Eq
import Mathlib.Tactic
open Relation


--- *** Relational Union ***

-- Compositional definition of union of relations. I should prove that this yeilds the set theoretic definition of union of pairs.
@[match_pattern]
def Relation.union (R : Relation α β) (S : Relation α β) :=  (split α) ▹ (R⊕S) ▹ (collapse β)


namespace Relation
infixl:50 "∪" => Relation.union
end Relation

-- We give the direct set-theoretic definition of a union of two relations.
def Relation.union_pairs_def (R : Relation α β) (S : Relation α β) : Pairs α β  := fun a b => eval R a b ∨ eval S a b

-- Proof that the compositional definition of union is equal to the set theoretic definiton.
theorem Relation.union_eval_eq_pairs (R : Relation α β) (S : Relation α β) : eval (R ∪ S) = union_pairs_def R S := by
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


-- Composition on the left distributes over union.
theorem comp_intersect_dist_left  {α β γ: Type u} (R: Relation α β)(S T: Relation β γ ): (R▹(S ∪ T)) ≈   ((R▹S) ∪ (R▹T)) := by
  simp [(·≈· ),eq,(·≤·), eval, domain, codomain]
  constructor
  · intro a c b Rab  S_or_Tbc
    cases S_or_Tbc with
    | inl Sbc =>
      apply Or.inl
      use b
    | inr Tbc =>
      apply Or.inr
      use b
  · intro a c h
    cases h with
    | inl E_RS =>
      obtain ⟨b, Rab, Sbc⟩ := E_RS
      use b
      simp_all
    | inr E_RT =>
      obtain ⟨b, Rab, Tbc⟩ := E_RT
      use b
      simp_all


-- Composition on the right distributes over union.
theorem comp_intersect_dist_right  {α β γ: Type u} (S T: Relation α  β  ) (R: Relation β  γ ): ((S ∪ T)▹R) ≈ ((S▹R) ∪ (T▹R)) := by
  simp [(·≈· ),eq,(·≤·), eval, domain, codomain]
  constructor
  · intro a c b S_or_Tab Rbc
    cases S_or_Tab with
    | inl Sab =>
      apply Or.inl
      use b
    | inr Tac =>
      apply Or.inr
      use b
  · intro a c E__SR_or_TR
    cases E__SR_or_TR with
    | inl E_SR =>
      obtain ⟨b, ⟨Sab, Rbc⟩ ⟩ := E_SR
      use b
      simp_all
    | inr E_TR =>
      obtain ⟨b, ⟨Tab, Rbc⟩ ⟩ := E_TR
      use b
      simp_all


-- TODO:
-- Union is contained in relative sum (both sides)
theorem sum_union_le_left {α β γ: Type u} (R: Relation α β) (S T: Relation β γ):
  ((R✦S) ∪ (R✦T)) ≤ (R✦(S ∪ T)) := by
  sorry




theorem sum_union_le_right {α β γ: Type u} (S T: Relation α β) (R: Relation β γ):
  ((S✦R) ∪ (T✦R)) ≤ ((S ∪ T)✦R) := by sorry
