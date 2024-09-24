import RelationalCalculus.Basic
import RelationalCalculus.Utility
import RelationalCalculus.Order
import RelationalCalculus.Eq
import RelationalCalculus.Union
import RelationalCalculus.Intersection
import RelationalCalculus.Residuals
import Mathlib.Tactic

open Utility
open Relation

universe u


-- Deeply a work in progress. Not useful yet.
namespace Relation
-- Gets the left image relation of R. That is the subrelation of R that is a subrelation of id and connects the left image of R.
def imgLeft {α β : Type u} (R : Relation α β) : Relation α α  :=
  let id_α := idR α
  R▹Rᵒ▹(id_α⁻▹R▹Rᵒ▹id_α⁻)⁻

-- theorem select_iff_leq_id {R : α β} : selectLeft R ≤ idR := by sorry



-- Gets the right image
def imgRight {α β : Type u} (R : Relation α β) : Relation β β  := imgLeft (Rᵒ)


-- Note: I'm starting to think my definition might have been wrong.
-- theorem img_sub_id {α β : Type u} (R: Relation α β ) : (imgLeft R) ≤ (idR α) := by
-- simp [(· ≤·), imgLeft, eval, domain, codomain]
-- intro a1 a2 a3 b a1Rb a3Rb h1
-- have h2 := h1 a3 b a1
-- have h3 := h1 a1 b a2
-- have h4 := h1 a3 b a2 -- got for contra
-- have h5 := h1 a2 b a1
-- have h6 := h1 a2 b a3 -- trival
-- have h7 := h1 a1 b a3 -- trival

-- -- have h4' : (¬a3 = a2 ∧ R.eval a2 b ∧ R.eval a3 b) → a3 = a2 := by
-- --   intro conj
-- --   obtain ⟨x1, ⟨ x2 , x3⟩ ⟩  := conj
-- --   exact h4 x1 x2 x3
-- have not_a2Rb : ¬(eval R a2 b) := by
--   by_contra a2Rb
--   -- have h4Conseq : (R.eval a2 b → R.eval a3 b → a3 = a2) -> a3 = a2 := by
--   --   intro ante
--   --   exact ante a2Rb a3Rb
--   have contra : ¬a3 = a2 → a3 = a2 := by
--     intro ante
--     exact h4 ante a2Rb a3Rb
