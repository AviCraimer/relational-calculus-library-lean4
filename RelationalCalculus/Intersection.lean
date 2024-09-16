import RelationalCalculus.Basic
import RelationalCalculus.Order
import RelationalCalculus.Eq
import RelationalCalculus.Union

namespace Relation

-- Compositional definition of intersection of relations.
-- TODO: Maybe I can define this using duality with union. That way I can get theorems for free.
@[match_pattern]
def intersect (R : Relation α β) (S : Relation α β) := comp (comp (copy α) (product R S)) (Relation.merge β)

infixl: 50 "∩" => intersect

-- We give the direct set-theoretic definition of an intersection of two relations.
def intersect_pairs_def (R : Relation α β) (S : Relation α β) : Pairs α β  := fun a b => (eval R) a b ∧ (eval S) a b

-- Proof that the compositional definition of intersection is equal to the set theoretic definiton.
theorem intersect_pairs_eq_eval (R : Relation α β) (S : Relation α β) : intersect_pairs_def R S = eval (R ∩ S)   := by
  symm
  apply funext
  intro a
  apply funext
  intro b
  simp [eval, intersect_pairs_def, intersect]
  constructor <;> sorry
  -- · intro ⟨a_1 b_1, ⟨ ⟨ aEqa1 , aEqb1⟩, ⟨Reval, Seval ⟩ ⟩ ⟩
  --   subst ha1 ha2 hb1 hb2
  --   exact ⟨hr, hs⟩
  -- intro ⟨hr, hs⟩
  -- use (b, b)
  -- constructor
  -- use (a, a)
  -- constructor <;> rfl


theorem intersect_union_eval {α β : Type u} (R S: Relation α β) : eval (R ∩ S) = eval ((R⁻ ∪ S⁻)⁻)  := by
simp [intersect, union, complement, eval, domain, codomain]
funext a c ; simp
constructor <;> intro h
· rcases h with ⟨a_1, b, ⟨ ⟨ a_eq_a1, a_eq_b ⟩, RandS ⟩⟩
  rw [a_eq_a1.symm] at RandS
  rw [a_eq_b.symm] at RandS
  exact RandS
· use a, a

-- DeMorgan Equivalence between intersection and union.
-- This lets us translate theorems about union to corresponding theorems about intersection.
theorem intersect_union_demorgan {α β : Type u} (R S: Relation α β) : (R ∩ S)  ≃  ((R⁻ ∪ S⁻)⁻) := by
simp [eq, (·≤ ·), intersect_union_eval ]

-- TODO
def intersect_union_convert   {α β : Type u} ( I: Relation α β ) : Relation α β  :=
  match I with
  | (intersect R S) => ((R⁻ ∪ S⁻)⁻)
  | _ => I



-- def union_intersect_convert  {α β : Type u} ( U: Relation α β ) : Relation α β  :=
-- match U with
--  | (union R S) => ((R⁻ ∩ S⁻)⁻)
--  | I' => I'

-- apply funext



-- Compositional Definition of Subtraction one relation from another.
def subtract {α β : Type u} (R S : Relation α β) : Relation α β :=
  let D := (R ∩ S)ᗮ
  let Disconnected := D▹R▹D
  Disconnectedᵒ


infixl: 60 "⊖" => subtract -- \ominus

-- TODO: Prove the composition definition of subtraction works as expected under evaluation
theorem subtract_eval {α β : Type u} (R S : Relation α β)(a:α)(b:β): (eval (R⊖S) a b) ↔ (eval R a b) ∧ ¬(eval S a b) := sorry


end Relation
