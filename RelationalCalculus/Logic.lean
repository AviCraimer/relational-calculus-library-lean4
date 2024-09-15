import RelationalCalculus.Basic
import RelationalCalculus.Order
import RelationalCalculus.Eq
import RelationalCalculus.Union
import RelationalCalculus.Intersection

open Classical
namespace Relation.logic
open Relation
notation "⋆" => PUnit.unit -- \*
notation "{⋆}" => PUnit --

abbrev PropR :=  Relation {⋆} {⋆}
abbrev TrueR : PropR := full {⋆} {⋆}
abbrev FalseR : PropR := empty {⋆} {⋆}


theorem bivaluedProps (R : PropR) (a b : {⋆}) : eval R a b = True ∨ eval R a b = False := by
    cases a ; cases b ;
    simp
    exact Classical.em (eval R ⋆ ⋆)

theorem biequivalentProps (R : PropR) : (R ≃ TrueR) ∨ (R ≃ FalseR) := by
  rewrite [← eval_eq_iff_eq]
  rw [or_iff_not_imp_left]
  intro h
  apply eval_to_eq
  funext a b
  simp [eval]
  have bv :=  (bivaluedProps R a b)
  exfalso
  sorry
  -- TODO almost there!


def andR (P Q: PropR) : PropR := TrueR ▹ (copy {⋆}) ▹ P ⊗ Q ▹ merge {⋆}
infixl: 90 " ∧ " => andR

def orR (P Q: PropR) : PropR :=  TrueR ▹ split {⋆} ▹ P ⊕ Q ▹ collapse {⋆}
infixl: 85 " ∨ " => orR

def notR (P: PropR) : PropR := P⁻
prefix: 95 "¬" => notR -- \neg


def IfThenR (P Q: PropR) : PropR := (¬P) ∨ Q
infixr : 83 " → " => IfThenR -- \imp


-- Turn any relation into a proposition by unit capping it with full on either side. Effectively this is the proposition that R is non-empty.
def existsR (R : Relation α β) : PropR := full {⋆} α ▹ R ▹ full β {⋆}
prefix: 83 "∃" => existsR


-- TODO
theorem not_exists_iff_empty (R : Relation α β) : ¬∃ R ≃ TrueR ↔  R ≃ empty α β := by
  -- Convert to eval
  sorry

-- Uses logical equivalency of ¬∃.¬P
def forAllR (R : Relation α β) := ¬existsR (R⁻)
prefix: 83 "∀" => forAllR
-- Note: I need to prove some more basic algeraic laws so I'm not always having to go back to eval.

-- TODO
theorem for_all_iff_full (R : Relation α β) : ∀ R ≃ TrueR ↔  R ≃ full α β := by sorry

-- We define a relational algebraic method of checking if relations are subsets using linear implication.
def subR (S R : Relation α β) : PropR :=
  full {⋆} β ▹ R ⊸ S ▹ full β {⋆}

infixl : 80 " ⊆ " => subR

-- TODO
-- theorem sub_rel_iff_leq {S R : Relation α β} : S ⊆ R ≃ TrueR ↔ S ≤ R := sorry


-- Gets the left image relation of R. That is the subrelation of R that is a subrelation of id and connects the left image of R.
def selectLeft {α β : Type u} (R : Relation α β) : Relation α α  :=
  let id_α := idR α
  R▹Rᵒ▹(id_α⁻▹R▹Rᵒ▹id_α⁻)⁻

-- theorem select_iff_leq_id {R : α β} : selectLeft R ≤ idR := by sorry

-- Gets the right image
def selectRight {α β : Type u} (R : Relation α β) : Relation β β  := selectLeft (Rᵒ)


-- Forall L, gets left selection and returns subset prop relations for if idR is subset of selection.
-- Recall that  a selection is always a subset of idR.
-- def totalImgL (R : Relation α β) : PropR :=
--   let Left := selectLeft R
--   idR ⊆ Left

--
-- def totalImgR (R : Relation α β) :PropR :=
--   let Right := selectRight R
--   idR ⊆ Right

-- Checks that R is total on right and left images
-- def totalImg (R : Relation α β) :PropR :=
--   totalImgR R ∧ totalImgL R
