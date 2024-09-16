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

-- theorem comp_respects_equiv {α β γ : Type u} (R R' : Relation α β) (S S' : Relation β γ) : (R ▹ S) ≈ (R' ▹ S') := by
--   simp [(·≈·), eq]
--   constructor
--   · -- Prove (R ▹ S) ≤ (R' ▹ S')
--     intros a c h
--     simp [Relation.eval, Relation.comp] at *
--     rcases h with ⟨b, hr, hs⟩
--     use b
--     constructor
--     · exact h1.1 a b hr
--     · exact h2.1 b c hs
--   · -- Prove (R' ▹ S') ≤ (R ▹ S)
--     intros a c h
--     simp [Relation.eval, Relation.comp] at *
--     rcases h with ⟨b, hr, hs⟩
--     use b
--     constructor
--     · exact h1.2 a b hr
--     · exact h2.2 b c hs

def RelationQuotient.comp {α β γ : Type u} (R : RelationQuotient α β) (S : RelationQuotient β γ) : RelationQuotient α γ :=
  Quotient.lift₂ (fun R' S' => Quotient.mk _ (Relation.comp R' S')) (fun R S R' S' h1 h2 => Quotient.sound (by
    sorry
    -- simp [(·≈·), eq, (·≤·), AntisymmRel]
    -- constructor <;> intro a c <;>
    -- simp [eval, domain] <;> intro b
    -- · intro Reval Seval
    --   use b
    --   have R'eval:  R'.eval a b := by rw [h1.symm] at Reval
    --   -- have S'eval:  S'.eval b c := by rw [h2.symm] at Reval
    --   -- have S.eval b c :
    -- · intro R'eval S'eval
    --   use b


  )) R S
