import RelationalCalculus.Basic
import RelationalCalculus.Order
import RelationalCalculus.Eq
open Relation


--- *** Relational Union ***

-- Compositional definition of union of relations. I should prove that this yeilds the set theoretic definition of union of pairs.
def Relation.union (R : Relation α β) (S : Relation α β) := comp (comp (Relation.split α) (coproduct R S)) (collapse β)

namespace Relation
infix: 50 "∪" => Relation.union
end Relation

-- We give the direct set-theoretic definition of a union of two relations.
def Relation.union.pairs_def (R : Relation α β) (S : Relation α β) : Pairs α β  := fun a b => (eval R) a b ∨ (eval S) a b

-- Proof that the compositional definition of union is equal to the set theoretic definiton.
theorem Relation.union.eval_eq_pairs (R : Relation α β) (S : Relation α β) : eval (Relation.union R S) = union.pairs_def R S := by
apply funext
intro a
apply funext
intro b
simp [Relation.eval, union.pairs_def, Relation.union]
constructor
intro ⟨c, ⟨c₁, h₁, h₂⟩, h₃⟩
cases c₁ <;> cases c <;> simp at h₁ h₂ h₃ <;> subst h₁<;> subst h₃
· exact Or.inl h₂
· exact Or.inr h₂
· intro h4
  cases h4 with
  | inl h4R =>
    use Sum.inl b
    constructor
    use Sum.inl a
    constructor
  | inr hS =>
    use Sum.inr b
    constructor
    use Sum.inr a
    constructor





theorem Relation.union.le_left (R S : Relation α β) : R ≤ Relation.union R S := by
  intros a b h
  simp [Relation.eval, Relation.union]
  use Sum.inl b
  constructor
  · use Sum.inl a
  · simp

theorem Relation.union.le_right (R S : Relation α β) : S ≤ Relation.union R S := by
  intros a b h
  simp [Relation.eval, Relation.union]
  use Sum.inr b
  constructor
  · use Sum.inr a
  · simp

theorem Relation.union.le_trans {R S T : Relation α β} (hR : R ≤ T) (hS : S ≤ T) : Relation.union R S ≤ T := by
  intros a b h
  simp [Relation.eval, Relation.union] at h
  rcases h with ⟨c, ⟨d, hd, hc⟩, hb⟩
  cases d
  case inl d' =>
    cases c
    case inl c' =>
      simp at hc hb
      subst hb
      subst hd
      exact hR _ _ hc
    case inr _ => contradiction
  case inr d' =>
    cases c
    case inl _ => contradiction
    case inr c' =>
      simp at hc hb
      subst hb
      subst hd
      exact hS _ _ hc


-- -- TODO
-- theorem Relation.union.comm  {α β : Type u } {R S : Relation α β } : (union S R) ≃ (union R S)   := by
--   apply eq_iff_eval_eq.2
--   intro a b
--   simp [union, eval]
--   constructor
--   intro h
--   rcases h with ⟨c, ⟨c₁, h₁, h₂⟩, h₃⟩
--   cases c₁ <;> cases c <;> simp at h₁ h₂ h₃ <;> subst h₁<;> subst h₃



-- -- TODO
-- theorem Relation.union.assoc {R S T : Relation α β} :
--     union (union R S) T ≃ union R (union S T) := by
--     := sorry
