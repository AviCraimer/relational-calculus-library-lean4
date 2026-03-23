import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic
import RelationalCalculus.CategoryTheory.Subcategory
import RelationalCalculus.CategoryTheory.ProductCategory
import RelationalCalculus.Utility
-- set_option pp.universes true
-- set_option diagnostics true
open Utility

namespace CategoryTheory
universe v u v' u'


/-- A packaged category. You might already have a similar definition. -/
structure RelCat  : Type (max (u+1) (v+1))  where
  carrier : Type u
  [hCategory : Category.{v} carrier]

namespace RelCat


instance : CoeSort RelCat (Type u) where
  coe R := R.carrier

-- Provide a Category instance for any `C : RelCat`.
instance (C : RelCat) : Category.{v} C.carrier := C.hCategory


-- A morphism from C to D is a subcategory of the product category C × D.

@[simp]
def Hom (C D : RelCat)  := Subcategory (C × D)

-- Identity: the reflexive subcategory of C × C.
def id (C : RelCat.{u,v}) : Subcategory (C  × C) where
  obj_subset P  :=  P.1 = P.2
  hom_subset {X Y} fg :=
    ((X.1 = X.2) ∧ (Y.1 = Y.2)) ∧ HEq fg.1 fg.2
  object_closure {X Y} f h := by
    simp at h
    exact h.1


  id_closure (X: C × C) :=  by
    simp
    intro Xeq
    obtain ⟨fst, snd⟩ := X
    simp_all only
    subst Xeq
    simp_all only [heq_eq_eq]

  comp_closure {X Y Z} {f} {g} hf hg  := by
    simp_all only [and_true, and_self, prod_comp, true_and]
    obtain ⟨X1, X2⟩ := X
    obtain ⟨Y1, Y2⟩ := Y
    obtain ⟨Z1, Z2⟩ := Z
    obtain ⟨XEq, right⟩ := hf
    obtain ⟨⟨ YEq, ZEq⟩, right_1⟩ := hg
    simp_all only
    subst ZEq XEq YEq
    simp_all only [heq_eq_eq]


def comp {C D E : RelCat.{u,v}} (R: Subcategory (C × D)) (S: Subcategory (D × E)) : Subcategory (C × E) where
  obj_subset P :=  ∃ (d : D), R.obj_subset (P.1, d) ∧ S.obj_subset (d, P.2)
  hom_subset {CE1 CE2} pair_of_morphisms_CE :=
    let m_c := pair_of_morphisms_CE.1
    let m_e  := pair_of_morphisms_CE.2

    ∃ (d1 d2 : D) (m_d : d1 ⟶ d2),
      let left_connection := R.hom_subset (X := (CE1.1, d1)) (Y := (CE2.1, d2) ) (m_c, m_d)
      let right_connection := S.hom_subset (X := (d1, CE1.2)) ( Y := (d2, CE2.2)) (m_d, m_e)
      left_connection ∧ right_connection

  object_closure {CE1 CE2} f h := by
    simp_all only
    obtain ⟨c1, e1⟩ := CE1
    obtain ⟨c2, e2⟩ := CE2
    obtain ⟨d1, d2, m_d, inR, inS⟩ := h
    have RObj := R.object_closure inR
    have SObj := S.object_closure inS
    obtain ⟨Rc1d1, Rc2d2⟩ := RObj
    obtain ⟨Sd1e1, Sd2e2⟩ := SObj
    constructor
    · use d1
    · use d2

  id_closure CE := by
    simp_all only [ProductCategory.prod_id]
    obtain ⟨c1, e1⟩ := CE
    simp_all only

    constructor
    · intro h
      obtain ⟨d, Rc1d, Rde1⟩ := h
      use d
      use d
      use 𝟙 d
      have hR := R.id_closure (c1, d)
      have hS := S.id_closure (d, e1)
      simp_all only [ProductCategory.prod_id, iff_true, true_and]
    · intro h
      obtain ⟨d1, d2, m_d, hR, hS⟩ := h
      have inR := R.object_closure hR
      have inS := S.object_closure hS
      obtain ⟨Rc1d1, Rc1d2 ⟩ := inR
      apply Exists.intro
      · apply And.intro
        · apply Rc1d2
        · simp_all only

  comp_closure {CE1 CE2 CE3 }{mc1_me1 : CE1 ⟶ CE2} {mc2_me2 : CE2 ⟶ CE3} hom1 hom2 := by
    simp_all


    obtain ⟨d1,d2, md1, Rmc1_md1, Smd1_me1 ⟩ := hom1
    obtain ⟨d3,d4, md2, Rmc2_md2, Smd2_me2 ⟩ := hom2

    -- Tricky problem. The issue is that in R, we have (mc, md) and (mc2, md2) and in S we have (md, me) and (md2, me2).

    -- If we look just at R, (mc, md) and (mc2, md2) need not be composable. We know that mc;mc2 is a composition in category C. However, the codomain of md and the domain of md2 need not be the same. This is possible because the codomain of mc can be related under R to both the codomain of md and the domain of md2, but those need not be the same objects. This splitting causes the problem. Actually, this is not a problem for R being a subcategory since if those morphisms aren't composable we are not required to relate mc;mc2 to anything in D. However, if mc;mc2 is left out in this way, then we we compose R and S, by dropping out the disconnected D morphisms, we end up with a pair of morphisms in C x E which are composable! Namely (mc, me) and (mc2, me2). We have (mc;mc2, me;me2) which is required to be in the subcategory by the composition closure axiom. However, it is not in the subcategory defined by the composition rule for R;S, since there is need not be any common morphism in D that both mc;mc2 and me;me2 are both related to.

    -- To solve this I'll have to delve deeper into how the Rel(Cat) construction works with the pullback square and image factorization. I must be missing something from my definition of comp, but I don't know what it is.



    obtain ⟨c1, e1⟩ := CE1
    obtain ⟨c2, e2⟩ := CE2
    obtain ⟨c3, e3⟩ := CE3
    obtain ⟨f_c , f_e ⟩ := f
    obtain ⟨g_c , g_e ⟩ := g
    simp_all only
    have ⟨ Rc1d1, Rc2d2 ⟩  := R.object_closure Rf_mc_md1
    have ⟨ Rc2d3, Rc3d4 ⟩  := R.object_closure Rg_mc_md2
    have ⟨ Sd1e1, Sd2e2 ⟩ := S.object_closure Sf_md1_me
    have ⟨ Sd3e2, Sd4e3 ⟩ := S.object_closure Sg_md2_me
    have Rclosure : R.comp_closure Rf_mc_md1 Rg_mc_md2 -- the endpoints of the D morphism don't match. Is this an issue in the definition?



--  ∃ d1 d2 m_d, R.hom_subset (f_c ≫ g_c, m_d) ∧ S.hom_subset (m_d, f_e ≫ g_e)

-- f_c : c1 ⟶ c2
-- f_e :  e1 ⟶  e2
-- g_c : c2 ⟶ c3
-- g_e :  e2 ⟶  e3
-- f_c ≫ g_c  : c1 -> c3
--  f_e ≫ g_e  : e1 -> e3






instance RelCatCategory : Category RelCat.{u,v} where
  Hom := Hom
  id := id
  comp := sorry
  id_comp := by sorry

  comp_id := by   sorry
  assoc   := by   sorry






------------------------------------------------------------
-- Composition: given R : Rel C D and S : Rel D E, define R ; S : Rel C E.
------------------------------------------------------------
def compRel {C D E : RelCat} (R : Rel C D) (S : Rel D E) : Rel C E :=

  hom_subset := λ {X Y} (f : X ⟶ Y),
    ∃ (d d' : D.carrier) (g : d ⟶ d'),
      R.hom_subset ⟨(X.1, d), (Y.1, d')⟩ ∧ S.hom_subset ⟨(d, X.2), (d', Y.2)⟩,
  object_closure := λ {X Y} f h,
  begin
    rcases h with ⟨d, hR, hS⟩,
    split; { use d, exact hR <|> exact hS }
  end,
  id_closure := λ X,
  begin
    split,
    { intro h, rcases h with ⟨d, hR, hS⟩,
      -- Use the id_closure for R and S (details omitted)
      sorry },
    { intro h,
      -- Again, use the id_closure of R and S to extract a suitable witness.
      sorry }
  end,
  comp_closure := λ {X Y Z} {f g} hf hg,
  begin
    rcases hf with ⟨d, d', g₁, hR₁, hS₁⟩,
    rcases hg with ⟨e, e', g₂, hR₂, hS₂⟩,
    -- Glue the witnesses using the composition properties of R and S.
    sorry
  end }

------------------------------------------------------------
-- Finally, we define our category whose objects are RelCat
-- and whose Hom sets are given by Rel.
------------------------------------------------------------
instance RelCatCategory {α : Type u} : Category (RelCat α) where
  Hom := Rel
  id := idRel
  comp := @compRel
  id_comp := by   sorry
  comp_id := by   sorry
  assoc   := by   sorry



end RelCat
