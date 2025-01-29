-- Unsorted Theorems about product ⊗
import RelationalCalculus.Basic
import RelationalCalculus.Order
import RelationalCalculus.Eq
import RelationalCalculus.Element
import RelationalCalculus.Empty
import Mathlib.Tactic

namespace Relation
open Relation



lemma product_equiv_congr  {α β γ δ : Type u}{ R R': Relation α β} {S S': Relation γ δ} (hR: R ≈ R') (hS: S ≈ S') : R⊗S  ≈ R'⊗S' := by
 simp [(· ≈ · ), eq, (· ≤ · ), eval]
 constructor <;> intro a c b d Rab Scd <;> simp at hR <;> simp at hS
 · constructor
   · rwa [hR.symm]
   · rwa [hS.symm]
 · constructor
   · rwa [hR]
   · rwa [hS]
