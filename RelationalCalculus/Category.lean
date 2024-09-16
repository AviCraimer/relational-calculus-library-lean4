import RelationalCalculus.Basic
import RelationalCalculus.Eq
import Mathlib.Tactic
import Mathlib.CategoryTheory.Category.Basic



open Relation
open CategoryTheory
#check Category

def SetObjects : Type (u+1) := Type u


-- I need to figure out how to life the constructors of Relation into the quotient type.

instance : Category.{(u+1),(u+1)} (Type u) where
  Hom := fun α β => RelationQuotient α β
  id := fun α => Quotient.mk idR α
  comp := fun R S => R ▹ S
  id_comp := by
   simp [idR]

  comp_id := sorry
  assoc := sorry
