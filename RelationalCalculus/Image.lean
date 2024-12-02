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
open Relation
-- Gets the image relation of R. That is the subrelation of identity β which includes elements that are second in pairs in R.
def img {α β : Type u} (R : Relation α β) : Relation β β   :=
  (Rᵒ▹ full α α ▹ R) ∩ (idR β )

abbrev imgCod {α β : Type u} (R : Relation α β) := img R

-- Gets the domain image of R.
def imgDom {α β : Type u} (R : Relation α β) : Relation α α  := img (Rᵒ)


-- We define the evaluation of the image of R as pairs directly.
def img_semantically {α β : Type u} (R : Relation α β) (b1 b2: β ) : Prop  :=  b1 = b2 ∧  ∃(a:α), R.eval a b1


theorem img_eval {α β : Type u} (R : Relation α β):  (img R).eval  = R.img_semantically := by
  simp [eval,  domain, codomain]
  funext b1 b2
  simp [img_semantically]
  constructor
  · intro h
    rcases h with ⟨a, ⟨_, h1⟩, h2⟩
    constructor
    · exact h1
    · let h3 := h2.right
      rcases h2 with ⟨b, hb ⟩
      rw [h1.symm] at h3
      exact h3
  · intro h
    rcases h with ⟨heq, ⟨a, ha⟩⟩
    exists b1
    constructor
    · exact ⟨ rfl,heq ⟩
    · constructor
      · exists a
      · exists a
        rwa [heq.symm]
