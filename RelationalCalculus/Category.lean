import RelationalCalculus.Basic
import RelationalCalculus.Eq
import RelationalCalculus.Quotient
import Mathlib.Tactic
import Mathlib.CategoryTheory.Category.Basic
set_option pp.proofs true

open RelationQuotient
open CategoryTheory

instance : Category (Type u) where
  Hom  (α : Type u)(β : Type u):=  RelationQuotient α β
  id (α : Type u) := idR α
  comp {α β γ : Type u} (R : RelationQuotient α β) (S :RelationQuotient β γ) :=  comp R S
  id_comp := id_comp
  comp_id := comp_id
  assoc := comp_assoc
