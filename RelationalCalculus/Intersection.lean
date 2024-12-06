import RelationalCalculus.Basic
import RelationalCalculus.Order
import RelationalCalculus.Eq
import RelationalCalculus.Union
import Mathlib.Tactic

namespace Relation
open Relation
-- Compositional definition of intersection of relations.
-- TODO: Maybe I can define this using duality with union. That way I can get theorems for free.
@[match_pattern]
def intersect (R : Relation α β) (S : Relation α β) := comp (comp (copy α) (product R S)) (Relation.merge β)

infixl: 50 "∩" => intersect

-- We give the direct set-theoretic definition of an intersection of two relations.
def intersect_pairs_def (R : Relation α β) (S : Relation α β) : Pairs α β  := fun a b => (eval R) a b ∧ (eval S) a b

-- Proof that the compositional definition of intersection is equal to the set theoretic definiton.
theorem intersect_eval_eq_pairs (R : Relation α β) (S : Relation α β) :  eval (R ∩ S) = intersect_pairs_def R S    := by
  simp [eval,  intersect, domain, codomain]
  funext a b
  simp
  constructor
  · intro Eab
    rcases Eab with ⟨a1, a2, ⟨ aEqa1, aEqa2⟩, Ra1b, Ra2b⟩
    rw [aEqa2.symm] at Ra2b
    rw [aEqa1.symm] at Ra1b
    simp [intersect_pairs_def]
    exact ⟨Ra1b, Ra2b⟩
  · intro RinterS
    simp [intersect_pairs_def] at RinterS
    rcases RinterS with ⟨Rab, Sab⟩
    use a
    simp_all only [true_and, exists_eq_left']



theorem intersect_union_eval {α β : Type u} (R S: Relation α β) : (R ∩ S) ≈  ((R⁻ ∪ S⁻)⁻)  := by
  simp [(·≈·), eq,(·≤·), eval, domain, codomain]
  constructor
  · intro a b Rab Sab
    simp_all only [and_self]
  · intro a b Rab Sab
    use a
    simp_all only [true_and, exists_eq_left']

#check imp_iff_not_or

theorem union_intersect_eval {α β : Type u} (R S: Relation α β) : (R ∪ S) ≈  ((R⁻ ∩ S⁻)⁻)  := by
  simp [(·≈·), eq,(·≤·), eval, domain, codomain]
  constructor
  · intro a b a_1 a_2
    simp_all only [false_or]
  · intro a b RS
    rw [imp_iff_not_or, not_not] at RS
    exact RS


-- Composition on the leftis monotonic relative to composition
theorem comp_intersect_le_left   {α β γ: Type u} (R: Relation α β)(S T: Relation β γ ): (R▹(S ∩ T)) ≤  ((R▹S) ∩ (R▹T)) := by
  simp [(·≤·), eval, domain, codomain]
  intro a c b Rab  Sbc Tbc
  use a
  simp_all only [true_and, exists_eq_left']
  constructor <;> use b

-- Composition on the right is monotonic relative to composition
theorem comp_intersect_le_right  {α β γ: Type u} (S T: Relation α  β  ) (R: Relation β  γ ): ((S ∩ T)▹R) ≤  ((S▹R) ∩ (T▹R)) := by
  simp [(·≤·), eval, domain, codomain]
  intro a c b Sab Tab Rbc
  use a
  use a
  constructor
  · simp_all
  · constructor <;> use b







-- DeMorgan Equivalence between intersection and union.
-- This lets us translate theorems about union to corresponding theorems about intersection.
-- theorem intersect_union_demorgan {α β : Type u} (R S: Relation α β) : (R ∩ S)  ≈  ((R⁻ ∪ S⁻)⁻) := by
-- simp [(·≈·), (·≤ ·), intersect_union_eval ]

-- -- TODO
-- def intersect_union_convert   {α β : Type u} ( I: Relation α β ) : Relation α β  :=
--   match I with
--   | (intersect R S) => ((R⁻ ∪ S⁻)⁻)
--   | _ => I



-- def union_intersect_convert  {α β : Type u} ( U: Relation α β ) : Relation α β  :=
-- match U with
--  | (union R S) => ((R⁻ ∩ S⁻)⁻)
--  | I' => I'

-- apply funext


-- TODO: I think this might be wrong. Might be better to define subtraction in the Inclusion.lean.
-- -- Compositional Definition of Subtraction one relation from another.
-- def subtract {α β : Type u} (R S : Relation α β) : Relation α β :=
--   let D := (R ∩ S)ᗮ
--   let Disconnected := D▹R▹D
--   Disconnectedᵒ


-- infixl: 60 "-" => subtract --

-- -- TODO: Prove the composition definition of subtraction works as expected under evaluation
-- theorem subtract_eval {α β : Type u} {R S : Relation α β} : ∀(a: α)(b:β),(eval (R-S) a b) =  ((eval R a b) → ¬(eval S a b)) := by
--  simp [eval,domain,codomain]
--  intro a b
--  constructor
--  · intro h Rab
--    rcases h with ⟨b1,⟨ a1, ⟨RnSa1b, Ra1b1⟩ ⟩, RnSab1⟩
--      · sorry
--    · sorry


end Relation
