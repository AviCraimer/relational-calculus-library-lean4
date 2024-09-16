import RelationalCalculus.Basic
import RelationalCalculus.Order
import RelationalCalculus.Eq
import Mathlib.Tactic
open Relation

-- Defines the type of relations quotiented by evaluation equivalence.
def RelationQuotient (α β : Type u) := Quotient (@instSetoidRelation α β)

def RelationQuotient.atomic {α β : Type u} (f : Relation.Pairs α β) : RelationQuotient α β :=
  Quotient.mk _ (Relation.atomic f)

def RelationQuotient.idR (α  : Type u) : RelationQuotient α α  :=
  Quotient.mk _ (Relation.idR α)

def RelationQuotient.pair {α β : Type u} (a : α) (b : β) : RelationQuotient α β :=
  Quotient.mk _ (Relation.pair a b)


def RelationQuotient.comp {α β γ : Type u} (R : RelationQuotient α β) (S : RelationQuotient β γ) : RelationQuotient α γ :=
  Quotient.lift₂ (fun R' S' => Quotient.mk _ (Relation.comp R' S')) (fun R S R' S' h1 h2 => Quotient.sound (by
    have RR'eval := eq_to_eval h1
    have SS'eval := eq_to_eval h2
    simp [(·≈·), (·≤·), AntisymmRel]
    constructor <;> intro a c <;>
    simp [eval, domain] <;> intro b
    · intro Reval Seval
      use b
      rw [RR'eval.symm, SS'eval.symm]
      exact ⟨Reval, Seval⟩
    · intro R'eval S'eval
      rw [RR'eval, SS'eval]
      exact ⟨b, ⟨R'eval, S'eval ⟩⟩
  )) R S
