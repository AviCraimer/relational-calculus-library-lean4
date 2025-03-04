import Mathlib.CategoryTheory.Category.Basic

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

-- S.hom_subset (?m.7830 (𝟙 c) (𝟙 d) (𝟙 c, 𝟙 d), ?m.7831 (𝟙 c) (𝟙 d) (𝟙 c, 𝟙 d))
-- All Messages (4)

lemma subcat_id_iff {C : Type u} [Category C] (S : Subcategory C) (X : C) :
  S.obj_subset X ↔ S.hom_subset (𝟙 X) :=
  S.id_closure X

@[simp]
lemma subcat_object_closure {X Y :C} [Category C] (S : Subcategory C) {f:(X ⟶ Y)} :  S.hom_subset f →  (S.obj_subset X) ∧ (S.obj_subset Y) := S.object_closure

@[simp]
lemma subcat_comp_iff {C : Type u} [Category C] (S : Subcategory C)
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
instance SubcategoryAsCategory {C : Type u} [hC: Category.{v} C] (S : Subcategory C) : Category.{v} (Carrier S) where
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


-- Define a product category on C × D.

instance ProductCategory (C : Type u) [Category.{v} C] (D : Type u') [Category.{v'} D] : Category (C × D) where
  Hom (X Y: C × D) :=  (X.1 ⟶ Y.1) × (X.2 ⟶ Y.2)
  id (X: C × D ) :=  (𝟙 X.1, 𝟙 X.2)
  comp {X Y Z: C × D } f g := (f.1 ≫ g.1, f.2 ≫ g.2)
  id_comp := by aesop_cat
  comp_id := by aesop_cat
  assoc   := by aesop_cat


def hom_to_prod {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {c c' : C} {d d' : D} (fg : (c, d) ⟶ (c', d')) :
   (c ⟶ c') × (d ⟶ d') :=
fg


def prod_to_hom {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {c c' : C} {d d' : D} (fg: (c ⟶ c') × (d ⟶ d'))  :
    ( (c, d) ⟶ (c', d')) :=
fg

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
