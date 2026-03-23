-- File: Subcategory.lean
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic


namespace CategoryTheory
/-- A subcategory of `C` :
-/

structure Subcategory (C : Type u) [Category.{v} C] : Type (max u v) where
  -- Predicates
  obj_subset  (c:C) : Prop
  hom_subset  {X Y : C}(f: X ⟶ Y): Prop

  -- Axioms
  object_closure {X Y :C}{f:(X ⟶ Y)} (h: hom_subset f): (obj_subset X) ∧ (obj_subset Y)

  id_closure (X: C): obj_subset X ↔ hom_subset (𝟙 X)

  comp_closure {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (hf: hom_subset f)(hg: hom_subset g)  :    hom_subset (f ≫ g)

lemma subcat_id_iff {C : Type u} [Category.{v} C] (S : Subcategory C) (X : C) :
  S.obj_subset X ↔ S.hom_subset (𝟙 X) :=
  S.id_closure X

lemma subcat_object_closure {X Y :C} [Category.{v} C] (S : Subcategory C) {f:(X ⟶ Y)} :  S.hom_subset f →  (S.obj_subset X) ∧ (S.obj_subset Y) := S.object_closure


lemma subcat_comp_iff {C : Type u} [Category.{v} C] (S : Subcategory C)
  {X Y Z : C}  {f : X ⟶ Y} {g : Y ⟶ Z} (hf: S.hom_subset f)(hg: S.hom_subset g) :  S.hom_subset (f ≫ g) :=
  S.comp_closure hf hg

namespace Subcategory

/-- The objects of a subcategory `S` are the objects of `C` satisfying `S.obj_subset`. -/
@[simp]
def Carrier {C : Type u} [Category.{v} C] (S : Subcategory C) :=
  { X : C // S.obj_subset X }

/-- For objects `X` and `Y` in `S.Carrier`, a morphism is a morphism in `C` that lies in the subcategory,
i.e. it satisfies `S.hom_subset`. -/
@[simp]
def Hom  {C : Type u} [Category.{v} C] (S : Subcategory C) (X Y : Carrier S) :=
  { f : X.val ⟶ Y.val // S.hom_subset f }

-- Every subcategory is a category
instance SubcategoryAsCategory {C : Type u} [hC: Category.{v} C] (S : Subcategory C) : Category (Carrier S) where
  Hom X Y := Hom S X Y
  id (Y:S.Carrier) := ⟨𝟙 Y.val, by
    simp [Carrier] at Y
    have h : S.obj_subset Y.val := by exact Y.property
    exact (S.id_closure Y.val).mp h
   ⟩
  comp {X Y Z} (f : Hom S X Y) (g : Hom S Y Z) :=
    ⟨f.val ≫ g.val, S.comp_closure f.property g.property ⟩
  id_comp f := by apply Subtype.ext; exact hC.id_comp f.val
  comp_id f := by apply Subtype.ext; exact hC.comp_id f.val
  assoc f g h := by apply Subtype.ext; exact hC.assoc f.val g.val h.val


@[simp]
lemma subcat_id_val {C : Type u} [Category C] (S : Subcategory C) (X : S.Carrier) :
    ((𝟙 (X : S.Carrier)) : Hom S X X).val = 𝟙 X.val :=
  rfl

@[simp]
lemma subcat_comp_val {C : Type u} [Category C] (S : Subcategory C)
  {X Y Z : S.Carrier} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (f ≫ g).val = f.val ≫ g.val :=
  rfl



end Subcategory
end CategoryTheory
