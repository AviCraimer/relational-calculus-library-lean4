-- File: ProductCategory.lean
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic

namespace CategoryTheory

-- Define a product category on C × D.
instance ProductCategory (C : Type u) [Category.{v} C] (D : Type u') [Category.{v'} D] : Category (C × D) where
  Hom (X Y: C × D) :=  (X.1 ⟶ Y.1) × (X.2 ⟶ Y.2)
  id (X: C × D ) :=  (𝟙 X.1, 𝟙 X.2)
  comp {X Y Z: C × D } f g := (f.1 ≫ g.1, f.2 ≫ g.2)
  id_comp := by aesop_cat
  comp_id := by aesop_cat
  assoc   := by aesop_cat

namespace ProductCategory
@[simp]
lemma prod_id {C : Type u} {D : Type u'} [Category C] [Category D]
  (X : C × D) :
  𝟙 X = (𝟙 X.1, 𝟙 X.2) :=
  rfl


@[simp]
lemma prod_comp {C : Type u} {D : Type u'} [Category C] [Category D]
  {X Y Z : C × D} (f : X ⟶ Y) (g : Y ⟶ Z) :
  f ≫ g = (f.1 ≫ g.1, f.2 ≫ g.2) :=
  rfl
end ProductCategory

def hom_to_prod {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {c c' : C} {d d' : D} (fg : (c, d) ⟶ (c', d')) :
   (c ⟶ c') × (d ⟶ d') :=
fg


def prod_to_hom {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {c c' : C} {d d' : D} (fg: (c ⟶ c') × (d ⟶ d'))  :
    ( (c, d) ⟶ (c', d')) :=
fg

end CategoryTheory
