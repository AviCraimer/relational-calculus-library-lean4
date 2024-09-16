import RelationalCalculus.Basic
import RelationalCalculus.Order
import RelationalCalculus.Eq
import Mathlib.Tactic
open Relation

-- Defines the type of relations quotiented by evaluation equivalence.
def RelationQuotient (α β : Type u) := Quotient (@instSetoidRelation α β)


namespace RelationQuotient
def atomic {α β : Type u} (f : Relation.Pairs α β) : RelationQuotient α β :=
  Quotient.mk _ (Relation.atomic f)

def idR (α  : Type u) : RelationQuotient α α  :=
  Quotient.mk _ (Relation.idR α)
#check idR
def pair {α β : Type u} (a : α) (b : β) : RelationQuotient α β :=
  Quotient.mk _ (Relation.pair a b)


def comp {α β γ : Type u} (R : RelationQuotient α β) (S : RelationQuotient β γ) : RelationQuotient α γ :=
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

theorem comp_id {X Y: Type u} : ∀ (Rq  : RelationQuotient X Y), comp Rq (idR Y) = Rq := by
apply Quotient.ind
intro R
apply Quotient.sound
simp [(·≈·), AntisymmRel, LE.le,Relation.eval]

theorem id_comp {X Y: Type u} : ∀ (Rq  : RelationQuotient X Y), comp (idR X) Rq = Rq := by
apply Quotient.ind
intro R
apply Quotient.sound
simp [(·≈·), AntisymmRel, LE.le,Relation.eval]

theorem comp_assoc {W X Y Z : Type u} :
∀
  (R : RelationQuotient W X)
  (S : RelationQuotient X Y)
  (T : RelationQuotient Y Z),
    (comp (comp R S) T) = (comp R (comp S T)) := by
  apply Quotient.ind
  intro R
  apply Quotient.ind
  intro S
  apply Quotient.ind
  intro T
  apply Quotient.sound
  simp [(·≈·), AntisymmRel, LE.le,Relation.eval, Relation.domain]
  constructor <;> intro a b
  · intro y x Re Se Te
    use x
    constructor
    · exact Re
    · use y
  · intro x Re y Se Te
    use y
    constructor
    · use x
    · exact Te


end RelationQuotient
