import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic
import RelationalCalculus.CategoryTheory.Subcategory
import RelationalCalculus.CategoryTheory.ProductCategory

namespace CategoryTheory
universe v u v' u'

/--
A relator between two categories consists of relations between objects and morphisms that respect identities, endpoints, and composition.
-/
structure Relator (C : Type u) [Category.{v} C] (D : Type u') [Category.{v'} D] where
  /-- Relation between objects of categories C and D -/
  rel_ob (c:C)(d:D) : Prop

  /-- Relation between morphisms of categories C and D -/
  rel_morph {X Y : C} {X' Y' : D}  (f:X ⟶ Y) (g:X' ⟶ Y') : Prop

  /-- Condition 1: Objects are related if and only if their identity morphisms are related -/
  id_rel (c : C) (d : D) : rel_ob c d ↔ rel_morph (𝟙 c) (𝟙 d)

  /-- Condition 2: For related morphisms, their source and target objects must be related -/
  endpoint_rel {X Y : C} {X' Y' : D} {f : X ⟶ Y} {g : X' ⟶ Y'} (h: rel_morph f g) : rel_ob X X' ∧ rel_ob Y Y'

  /-- Condition 3: Composition is preserved within the image of the relations  -/
  comp_rel {X Y Z : C} {X' Y' Z' : D}
    {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} {g₁ : X' ⟶ Y'} {g₂ : Y' ⟶ Z'} (h1: rel_morph f₁ g₁)(h2:  rel_morph f₂ g₂) : rel_morph (f₁ ≫ f₂) (g₁ ≫ g₂)



-- Given a Relator, define a subcategory of the product category C × D.
def Relator.toSubcategory {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (R : Relator C D) : Subcategory (C × D) where
  obj_subset (X : C × D)  :=  R.rel_ob X.1 X.2
  hom_subset {X Y : C × D} (f : X ⟶ Y)  :=
    R.rel_morph f.1 f.2
  object_closure {X Y: C × D} (f : X ⟶ Y) h := R.endpoint_rel h

  id_closure (X: C × D)  := by
    have h1 := (R.id_rel X.1 X.2)
    simp
    exact h1

  comp_closure {X Y Z : C × D} (f : X ⟶ Y) (g : Y ⟶ Z)  := by
    simp
    intro hf hg
    exact R.comp_rel hf hg


def Subcategory.toRelator {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (S : Subcategory (C × D)) : Relator C D where
  rel_ob c d := S.obj_subset (c, d)
  rel_morph {c c' : C} {d d' : D} (f : c ⟶ c') (g : d ⟶ d') : Prop :=
    let fg : ( c ⟶ c') ×  ( d ⟶ d') :=  (f,g)
    S.hom_subset (prod_to_hom fg)

  id_rel (c : C) (d : D) := by
    have h1 := S.id_closure (c, d)
    simp [ prod_to_hom]
    simp [prod_comp] at h1
    exact h1

  endpoint_rel {X Y : C} {X' Y' : D} {f : X ⟶ Y} {g : X' ⟶ Y'} (h: S.hom_subset (f, g)) :=
    S.object_closure h

  comp_rel {X Y Z : C} {X' Y' Z' : D} {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} {g₁ : X' ⟶ Y'} {g₂ : Y' ⟶ Z'}
    (h1: S.hom_subset (prod_to_hom (f₁, g₁))) (h2: S.hom_subset (prod_to_hom (f₂, g₂))) := S.comp_closure h1 h2


-- Here we prove that relators from C to D are equivalent (isomorphic) to subcategories of the product category C × D. This is precisely analogous to how set-based relations are isomorphic to subsets of the Cartesian product. This supports the idea that Relators are a natural definition of relations between categories.
def relatorEquivSubcategory {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] :
  Relator C D ≃ Subcategory (C × D) where
  toFun R := R.toSubcategory
  invFun S := S.toRelator
  left_inv := by
    intro R
    rfl
  right_inv :=
    by
      intro S
      rfl


end CategoryTheory
