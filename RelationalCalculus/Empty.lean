-- Theorems about the empty relation which do not fit in other operations. For theorems related to other operations, look for the Empty.lean file in the relevant folder.

import RelationalCalculus.Basic
import RelationalCalculus.Order
import RelationalCalculus.Eq
import RelationalCalculus.Element
import Mathlib.Tactic

namespace Relation
open Relation

@[simp]
theorem empty_eval_false {α β : Type u} : (empty α β).eval = fun (_:α)(_:β) => False := by
  funext
  simp [eval]


theorem not_false_exists_pair {α β :Type u} (f: Pairs α β) : (¬ f = fun (_:α)(_:β) => False) = ∃ (a:α)(b:β), f a b = True := by
    simp_all only [eq_iff_iff, iff_true]
    apply Iff.intro
    · intro h'
      by_contra
      · have contra : f = fun (_:α)(_:β) => False := by
          funext a b
          simp_all only [not_exists]
        contradiction
    · intro a
      obtain ⟨w, h⟩ := a
      obtain ⟨w_1, h⟩ := h
      apply Aesop.BuiltinRules.not_intro
      intro a
      subst a
      simp_all only
