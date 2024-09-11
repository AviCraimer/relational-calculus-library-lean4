import  «RelationalCalculus».Basic
import  «RelationalCalculus».Order
import  «RelationalCalculus».Eq
import  «RelationalCalculus».Union

namespace Relation

-- Compositional definition of intersection of relations.
def intersection (R: Relation α β) (S: Relation α β) := comp (comp (copy α) (product R S)) (Relation.merge β)

infix: 50 "∩" => intersection


-- We give the direct set-theoretic definition of an intersection of two relations.
def intersect.pairs_def (R: Relation α β) (S: Relation α β): Pairs α β  := fun a b => (eval R) a b ∧ (eval S) a b

-- Proof that the compositional definition of intersection is equal to the set theoretic definiton.
theorem intersect.pairs_eq_eval (R: Relation α β) (S: Relation α β) : intersect.pairs_def R S  = eval (intersection R S)   := by
symm
apply funext
intro a
apply funext
intro b
simp [eval, intersect.pairs_def, intersection]
constructor
intro ⟨⟨c1, c2⟩, ⟨⟨a1, a2⟩, ⟨ha1, ha2⟩, hr, hs⟩, ⟨hb1, hb2⟩⟩
subst ha1
subst ha2
subst hb1
subst hb2
exact ⟨hr, hs⟩
intro ⟨hr, hs⟩
use (b, b)
constructor
use (a, a)
constructor <;> rfl


-- Compositional Definition of Subtraction one relation from another.
def subtract {α β :Type u} (R S: Relation α β ): Relation α β :=
  let D := (R ∩ S)ᗮ
  let Disconnected := D▹R▹D
  Disconnectedᵒ

-- TODO Prove this works with evaluation

infix: 50 "-" => subtract
