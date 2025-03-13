import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic
import Mathlib.Logic.Basic
import RelationalCalculus.CategoryTheory.Subcategory
import RelationalCalculus.CategoryTheory.ProductCategory
import RelationalCalculus.Utility
namespace CategoryTheory
universe v u v' u'
open Utility


/--
A relator between two categories consists of relations between objects and morphisms that respect identities, endpoints, and composition.
-/
structure Relator (C : Type u) [Category.{v} C] (D : Type u') [Category.{v'} D] where
  /-- Relation between objects of categories C and D -/
  rel_ob (c:C)(d:D) : Prop

  /-- Relation between morphisms of categories C and D -/
  rel_morph {X Y : C} {X' Y' : D}  (f:X ⟶ Y) (g:X' ⟶ Y') : Prop

  /-- Condition 1: Objects are related if and only if their identity morphisms are related -/
  obj_id_iff (c : C) (d : D) : rel_ob c d ↔ rel_morph (𝟙 c) (𝟙 d)

  /-- Condition 2: For related morphisms, their source and target objects must be related -/
  object_closure {X Y : C} {X' Y' : D} {f : X ⟶ Y} {g : X' ⟶ Y'} (h: rel_morph f g) : rel_ob X X' ∧ rel_ob Y Y'

  /-- Condition 3: Composition is preserved within the image of the relations  -/
  comp_closure {X Y Z : C} {X' Y' Z' : D}
    {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} {g₁ : X' ⟶ Y'} {g₂ : Y' ⟶ Z'} (h1: rel_morph f₁ g₁)(h2:  rel_morph f₂ g₂) : rel_morph (f₁ ≫ f₂) (g₁ ≫ g₂)



-- Given a Relator, define a subcategory of the product category C × D.
def Relator.toSubcategory {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (R : Relator C D) : Subcategory (C × D) where
  obj_subset (X : C × D)  :=  R.rel_ob X.1 X.2
  hom_subset {X Y : C × D} (f : X ⟶ Y)  :=
    R.rel_morph f.1 f.2
  object_closure {X Y: C × D} (f : X ⟶ Y) h := R.object_closure h

  id_closure (X: C × D)  := by
    have h1 := (R.obj_id_iff X.1 X.2)
    simp
    exact h1

  comp_closure {X Y Z : C × D} (f : X ⟶ Y) (g : Y ⟶ Z)  := by
    simp
    intro hf hg
    exact R.comp_closure hf hg


def Subcategory.toRelator {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (S : Subcategory (C × D)) : Relator C D where
  rel_ob c d := S.obj_subset (c, d)
  rel_morph {c c' : C} {d d' : D} (f : c ⟶ c') (g : d ⟶ d') : Prop :=
    let fg : ( c ⟶ c') ×  ( d ⟶ d') :=  (f,g)
    S.hom_subset (prod_to_hom fg)

  obj_id_iff (c : C) (d : D) := by
    have h1 := S.id_closure (c, d)
    simp [ prod_to_hom]
    simp [prod_comp] at h1
    exact h1

  object_closure {X Y : C} {X' Y' : D} {f : X ⟶ Y} {g : X' ⟶ Y'} (h: S.hom_subset (f, g)) :=
    S.object_closure h

  comp_closure {X Y Z : C} {X' Y' Z' : D} {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} {g₁ : X' ⟶ Y'} {g₂ : Y' ⟶ Z'}
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


---


---COMPOSITION OF RELATORS---

@[simp]
def relComp {α : Type u1}  {β  : Type u2} {γ : Type u3} (R: α → β → Prop )(S: β  → γ  → Prop) (a: α ) (c: γ ) := ∃ (b:β ), R a b ∧ S b c

@[simp]
def preComp {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E] {c1 c2 : C} {e1 e2 : E}  (R: Relator C D) (S: Relator D E) (f: c1 ⟶ c2) (h: e1 ⟶ e2) := (∃ (d1 d2 :D) (g:d1 ⟶ d2 ), R.rel_morph f g ∧ S.rel_morph g h)


inductive ReloCompData {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E] : ∀  (R: Relator C D) (S: Relator D E) {c1 c2 : C} {e1 e2 : E}, (c1 ⟶ c2) → (e1 ⟶ e2) → Type (max u u' u'' v v' v'')
| base (R: Relator C D) (S: Relator D E) {c1 c2 : C} {e1 e2 : E} {f: c1 ⟶ c2} {h: e1 ⟶ e2} (inRS: preComp R S f h)  : ReloCompData  R S f h
| comp  (R: Relator C D) (S: Relator D E) (f: c1 ⟶ c3) (h: e1 ⟶ e3) {c2: C} {e2:E} (f1: c1 ⟶ c2 )(f2: c2 ⟶ c3) (h1: e1 ⟶ e2 )(h2: e2 ⟶ e3)(ffEqf: f1≫f2 = f )(hhEqh: h1≫h2 = h) (f1h1: ReloCompData R S f1 h1) (f2h2: ReloCompData R S f2 h2) : ReloCompData R S f h

def ReloCompData.isBase {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E](R: Relator C D) (S: Relator D E) {c1 c3 : C} {e1 e3 : E} (f:c1 ⟶ c3)(h:e1 ⟶ e3)(data: ReloCompData R S f h) :=
    ∃ (inRS: preComp R S f h), data = ReloCompData.base R S inRS

def ReloCompData.isComp {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E](R: Relator C D) (S: Relator D E) {c1 c3 : C} {e1 e3 : E} (f:c1 ⟶ c3)(h:e1 ⟶ e3)(data: ReloCompData R S f h) :=
    ∃ (c2: C)(e2:E)(f1: c1 ⟶ c2 )(f2: c2 ⟶ c3)(h1: e1 ⟶ e2 )(h2: e2 ⟶ e3)(ffEqf: f1≫f2 = f )(hhEqh: h1≫h2 = h) (f1h1: ReloCompData R S f1 h1) (f2h2: ReloCompData R S f2 h2),
      data = ReloCompData.comp R S f h f1 f2 h1 h2 ffEqf hhEqh f1h1 f2h2

lemma ReloCompData.base_not_comp {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E](R: Relator C D) (S: Relator D E) {c1 c3 : C} {e1 e3 : E} (f:c1 ⟶ c3)(h:e1 ⟶ e3)(data: ReloCompData R S f h) : data.isBase → (¬ data.isComp) :=by
    simp [isBase, isComp]
    aesop
#check not_iff
lemma ReloCompData.comp_not_base  {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E](R: Relator C D) (S: Relator D E) {c1 c3 : C} {e1 e3 : E} (f:c1 ⟶ c3)(h:e1 ⟶ e3)(data: ReloCompData R S f h) : data.isComp → (¬ data.isBase) :=by
    simp [isBase, isComp]
    aesop

lemma ReloCompData.not_base_and_comp  {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E](R: Relator C D) (S: Relator D E) {c1 c3 : C} {e1 e3 : E} (f:c1 ⟶ c3)(h:e1 ⟶ e3)(data: ReloCompData R S f h) : ¬ (data.isBase ∧  data.isComp )  := by
simp only [isBase, isComp]
aesop


-- (a ∧ ¬ b) ∨ (b ∧ ¬ a)
lemma ReloCompData.base_xor_comp  {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E]{R: Relator C D} {S: Relator D E} {c1 c3 : C} {e1 e3 : E} {f:c1 ⟶ c3}{h:e1 ⟶ e3}(data: ReloCompData R S f h) :  Xor' data.isBase  data.isComp  := by
  rw [xor_iff_iff_not]
  simp only [isBase, isComp] at *
  constructor
  · intro hyp
    obtain ⟨hyp2, hyp3⟩ := hyp
    aesop
  · intro hyp
    by_cases isBase R S f h data
    · assumption
    · have hyp := ReloCompData.not_base_and_comp R S f h data
      rw [not_forall_not.symm]
      cases data with
      | base f h inRS =>
        by_contra  cn
        have nhyp := (cn inRS)
        aesop
      | comp R S f h f1 f2 h1 h2 fEqff hEqhh data1 data2 =>
        subst hEqhh fEqff
        simp_all only [comp.injEq, exists_and_left, exists_and_right, exists_prop', nonempty_prop, exists_eq_left',
          heq_eq_eq, true_and, exists_eq', and_true, and_self, not_true_eq_false]




-- Subtype that is built with composition
-- We might not need this
@[simp]
def ReloCompData.Comp {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E](R: Relator C D) (S: Relator D E) {c1 c3 : C} {e1 e3 : E} (f:c1 ⟶ c3)(h:e1 ⟶ e3) :=
  { data: ReloCompData R S f h  //
    ∃ (c2: C)(e2:E)(f1: c1 ⟶ c2 )(f2: c2 ⟶ c3)(h1: e1 ⟶ e2 )(h2: e2 ⟶ e3)(ffEqf: f1≫f2 = f )(hhEqh: h1≫h2 = h) (f1h1: ReloCompData R S f1 h1) (f2h2: ReloCompData R S f2 h2),
      data = ReloCompData.comp R S f h f1 f2 h1 h2 ffEqf hhEqh f1h1 f2h2
  }



def ReloCompData.obj_rel {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E]
  {R: Relator C D} {S: Relator D E} {c1 c2 : C} {e1 e2 : E} {f : c1 ⟶ c2} {h : e1 ⟶ e2}
  (data: ReloCompData R S f h) : (relComp R.rel_ob S.rel_ob) c1 e1 ∧ (relComp R.rel_ob S.rel_ob) c2 e2 :=
  match data with
  | base  R S inRS =>
      let ⟨d1, d3, g, Rfg, Sgh⟩ := inRS
      let ⟨Rc1d1, Rc2d3⟩ := R.object_closure Rfg
      let ⟨Sd1e1, Sd3e2⟩ := S.object_closure Sgh
      ⟨⟨d1, Rc1d1, Sd1e1⟩, ⟨d3, Rc2d3, Sd3e2⟩⟩
  | comp R S _ _ _ _ _ _ _ _ data1 data2 =>
      let ⟨src1, _⟩ := data1.obj_rel
      let ⟨_, tgt2⟩ := data2.obj_rel
      ⟨src1, tgt2⟩

def relo_morph_comp {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E]
  (R: Relator C D) (S: Relator D E) {c1 c3 : C} {e1 e3 : E} (f: c1 ⟶ c3) (h: e1 ⟶ e3) : Prop :=
  Nonempty (ReloCompData R S f h)

theorem relo_morph_comp.condition {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E]  {R: Relator C D} {S: Relator D E} {c1 c3 : C} {e1 e3 : E} {f: c1 ⟶ c3} {h: e1 ⟶ e3} (hyp: relo_morph_comp R S f h) : preComp R S f h ∨  (∃ (c2: C)(e2:E)(f1: c1 ⟶ c2 )(f2: c2 ⟶ c3)(h1: e1 ⟶ e2 )(h2: e2 ⟶ e3)(ffEqf: f1≫f2 = f )(hhEqh: h1≫h2 = h), relo_morph_comp  R S f1 h1  ∧  relo_morph_comp R S f2 h2) := by

    by_cases preComp R S f h
    · left
      assumption
    · right
      rename_i catC catD notPreComp
      have hypCopy := hyp
      simp [relo_morph_comp] at hyp

      obtain ⟨data⟩ := hyp
      have baseOrComp := ReloCompData.base_xor_comp data
      simp [Xor'] at baseOrComp
      have notBase : ¬ data.isBase := by
        simp only [ReloCompData.isBase]
        simp_all only [preComp, not_exists, not_and, isEmpty_Prop, not_false_eq_true, implies_true, IsEmpty.exists_iff]
      simp_all only [preComp, not_exists, not_and, false_and, not_false_eq_true, and_true, false_or, exists_and_left,
        exists_prop', nonempty_prop]
      simp [ReloCompData.isComp] at baseOrComp
      obtain ⟨c2,e2, f1,f2,h1,h2,ffEqf, hhEqh,  ⟨f1h1, f2h2, hypData ⟩   ⟩ := baseOrComp
      use c2, e2, f1, f2, h1
      subst hhEqh ffEqf
      simp_all only [true_and]
      constructor
      · simp [relo_morph_comp]
        exact Nonempty.intro f1h1
      · use h2
        constructor
        · rfl
        · exact Nonempty.intro f2h2






-- Something isn't right here.
-- theorem relo_morph_comp.assocr  {C D E I} [Category C] [Category D] [Category E] [Category I] {c1 c3: C} {i1 i3: I}
--     (R : Relator C D) (S : Relator D E) (T : Relator E I) (f:  c1  ⟶ c3) (j: i1  ⟶ i3) : (relo_morph_comp (relo_morph_comp R S) T) = relo_morph_comp  R (relo_morph_comp S T)   := by


def ReloCompData.identity_implies_rel_ob {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E]
  {R: Relator C D} {S: Relator D E} {c : C} {e : E}
  (data: ReloCompData R S (𝟙 c) (𝟙 e)) : relComp R.rel_ob S.rel_ob c e :=
  (data.obj_rel).1  -- The first component of obj_rel gives us exactly what we need

theorem comp_obj_id_iff {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E]
  (R: Relator C D) (S: Relator D E) (c : C) (e : E) :
  relComp R.rel_ob S.rel_ob c e ↔ relo_morph_comp R S (𝟙 c) (𝟙 e) := by
  constructor
  · intro h
    simp [relo_morph_comp]
    obtain ⟨d, Rcd, Sde⟩ := h
    -- Construct a base case for ReloCompData
    use ReloCompData.base R S ⟨d, d, 𝟙 d, (R.obj_id_iff c d).mp Rcd, (S.obj_id_iff d e).mp Sde⟩
  · intro h
    simp [relo_morph_comp] at h
    obtain ⟨data⟩ := h
    -- Use our helper function
    exact data.identity_implies_rel_ob


theorem comp_object_closure {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E]
   {R: Relator C D} {S: Relator D E} {c1 c3 : C} {e1 e3 : E} {f : c1 ⟶ c3} {h : e1 ⟶ e3}
   (morph: relo_morph_comp R S f h) :
   (relComp R.rel_ob S.rel_ob) c1 e1 ∧ (relComp R.rel_ob S.rel_ob) c3 e3 := by
   simp [relo_morph_comp] at morph
   obtain ⟨data⟩ := morph
   exact data.obj_rel


def Relator.comp {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E]  (R: Relator C D) (S: Relator D E) : Relator C E where
  rel_ob :=  (relComp R.rel_ob S.rel_ob)
  rel_morph {X Y : C} {X' Y' : E} f h := relo_morph_comp R S f h
  obj_id_iff c e := comp_obj_id_iff R S c e
  object_closure {c1 c3: C} {e1 e3: E} f h morph  :=  comp_object_closure morph
  comp_closure {c1 c2 c3 : C} {e1 e2 e3 : E} {f1 : c1  ⟶ c2} {f2 : c2 ⟶ c3} {h1 : e1 ⟶ e2} {h2 : e2 ⟶ e3}(h1_rel: relo_morph_comp R S f1 h1) (h2_rel: relo_morph_comp R S f2 h2) := by
    simp [relo_morph_comp] at *
    obtain ⟨data1⟩ := h1_rel
    obtain ⟨data2⟩ := h2_rel
    -- Use the comp constructor to build a composite relation
    use ReloCompData.comp R S (f1 ≫ f2) (h1 ≫ h2) f1 f2 h1 h2 rfl rfl data1 data2


lemma Relator.rel_morph_to_preComp {C D E } [Category C] [Category D] [Category E]  {R : Relator C D} {S : Relator D E} {c1 c3 : C}{d1 d3: D} { e1 e3: E} {f:  c1  ⟶ c3 } {g: d1  ⟶ d3}{h: e1  ⟶ e3}(Rfg : R.rel_morph f g) (Sgh : S.rel_morph g h ):  preComp R S f h := by
  simp ; use d1, d3, g

lemma Relator.preComp_to_rel_morph {C D E } [Category C] [Category D] [Category E]  {R : Relator C D} {S : Relator D E} {c1 c3 : C} { e1 e3: E} {f:  c1  ⟶ c3 } {h: e1  ⟶ e3} (preCompST: preComp R S f h):  (R.comp S).rel_morph f h  := by
  simp_all only [preComp, comp, relo_morph_comp]
  exact Nonempty.intro (ReloCompData.base R S preCompST )

-- Showing that composition of morphism relations are transitive and associative  for the base case.
lemma Relator.morph_comp_base_case_trans_assoc  {C D E I} [Category C] [Category D] [Category E] [Category I] {i1 i3: I} {R : Relator C D} {S : Relator D E} {T : Relator E I}{c1 c3 : C} {d1 d3 : D} {e1 e3 : E} {f:  c1  ⟶ c3 }{g: d1 ⟶ d3}{h: e1 ⟶ e3} {j: i1  ⟶ i3}(Rfg : R.rel_morph f g)(Sgh : S.rel_morph g h) (Thj : T.rel_morph h j) : ((R.comp S).comp T).rel_morph f j ∧ (R.comp (S.comp T)).rel_morph f j := by
  simp [comp]

  -- RS side
  let RS := R.comp S

  have preCompRSfh : preComp R S f h := Relator.rel_morph_to_preComp Rfg Sgh

  let dataRSfh : ReloCompData R S f h := ReloCompData.base R S preCompRSfh

  have RSfh : (R.comp S).rel_morph f h := by exact Nonempty.intro dataRSfh

  have preCompRS_Tfj : preComp RS T f j := Relator.rel_morph_to_preComp RSfh Thj

  let dataRS_Tfj : ReloCompData RS T f j := ReloCompData.base RS T preCompRS_Tfj

  -- ST side
  let ST := S.comp T
  have preCompRSgj : preComp S T g j := Relator.rel_morph_to_preComp Sgh Thj
  let dataSTgj : ReloCompData S T g j := ReloCompData.base S T preCompRSgj
  have STgj : (S.comp T).rel_morph g j := by exact Nonempty.intro dataSTgj
  have preCompR_STfj : preComp R ST f j := Relator.rel_morph_to_preComp Rfg STgj
  let dataR_STfj : ReloCompData R ST f j := ReloCompData.base R ST preCompR_STfj

  constructor
  · exact Nonempty.intro dataRS_Tfj
  · exact Nonempty.intro dataR_STfj



theorem Relator.rel_morp_assocr  {C D E I} [Category C] [Category D] [Category E] [Category I] {c1 c3: C} {i1 i3: I} (R : Relator C D) (S : Relator D E) (T : Relator E I){c1 c3 : C} {e1 e3 : E} {f:  c1  ⟶ c3 } {j: i1  ⟶ i3}   : ((R.comp S).comp T).rel_morph f j = (R.comp (S.comp T)).rel_morph f j  := by
  let RS := R.comp S
  let ST := S.comp T
  simp only [eq_iff_iff]
  constructor <;> intro hyp
  · simp only [comp] at *
    have hyp2 := relo_morph_comp.condition hyp
    simp_all only [preComp, exists_and_left, exists_prop', nonempty_prop]

    cases hyp2 with
    | inl hBaseOuter =>
      obtain ⟨e1, e3, h, RSfh, Thj⟩ :=   hBaseOuter
      have hyp3 :=  relo_morph_comp.condition RSfh
      simp [relo_morph_comp]


      cases hyp3 with
      | inl hBaseInner =>
        obtain ⟨d1, d3, g, Rfg, Sgh⟩ :=  hBaseInner
        have preCompST := Relator.rel_morph_to_preComp Sgh Thj
        have STgj :=  Relator.preComp_to_rel_morph preCompST
        have preCompR_ST : preComp R ST f j := Relator.rel_morph_to_preComp Rfg  STgj
        have  data : ReloCompData R ST f j := ReloCompData.base R ST  preCompR_ST
        exact Nonempty.intro data
      | inr h_2 =>
        -- obtain ⟨w, h_1⟩ := h_2
        -- obtain ⟨w_1, h_1⟩ := h_1
        -- obtain ⟨w_2, h_1⟩ := h_1
        -- obtain ⟨w_3, h_1⟩ := h_1
        -- obtain ⟨w_4, h_1⟩ := h_1
        -- obtain ⟨left, right⟩ := h_1
        -- obtain ⟨w_5, h_1⟩ := right
        -- obtain ⟨left_1, right⟩ := h_1
        -- obtain ⟨left_2, right⟩ := right
        -- subst left_1 left_2
        sorry



    | inr h_1 =>
      obtain ⟨w, h⟩ := h_1
      obtain ⟨w_1, h⟩ := h
      obtain ⟨w_2, h⟩ := h
      obtain ⟨w_3, h⟩ := h
      obtain ⟨w_4, h⟩ := h
      obtain ⟨left, right⟩ := h
      obtain ⟨w_5, h⟩ := right
      obtain ⟨left_1, right⟩ := h
      obtain ⟨left_2, right⟩ := right
      subst left_1 left_2
      sorry



  · sorry




theorem ReloCompData.assocr  {C D E I} [Category C] [Category D] [Category E] [Category I] {c1 c3: C} {i1 i3: I} {f:  c1  ⟶ c3 } {j: i1  ⟶ i3}
    (R : Relator C D) (S : Relator D E) (T : Relator E I) (RS_T: ReloCompData (R.comp S) T f j) : Nonempty (ReloCompData R (S.comp T) f j)  := by
      rename_i catC catD catE catI
      simp [Relator.comp, relo_morph_comp] at RS_T
      condition

      let ST := S.comp T

      have f1: c1 ⟶ c2
      have f2: c2 ⟶ c3
      have j1: c2 ⟶ c3
      have j1: c2 ⟶ c3

      let data : ReloCompData R ST f j := comp R ST f j f1 f2 j1 j2 ffEqf jjEqj f1j1 f2j2

    -- comp  (R: Relator C D) (S: Relator D E) (f: c1 ⟶ c3) (h: e1 ⟶ e3) {c2: C} {e2:E} (f1: c1 ⟶ c2 )(f2: c2 ⟶ c3) (h1: e1 ⟶ e2 )(h2: e2 ⟶ e3)(ffEqf: f1≫f2 = f )(hhEqh: h1≫h2 = h) (f1h1: ReloCompData R S f1 h1) (f2h2: ReloCompData R S f2 h2) : ReloCompData R S f h

      cases RS_T  with
      | @base R S c1 c2 i1 i2 f j inRS  =>
        obtain ⟨e1, e2, h, ⟨dataRSfh⟩ , Thj ⟩ := inRS



        cases dataRSfh with
        | @base R S c1 c2 e1 e2 f h RSProp =>

            exact RSProp
        | @comp R S c1 c3 e1 e3 f h c2 e2 f1 f2 h1 h2 ffEf hhEqh f1h1 f2h2 hyp1 hyp2  => sorry


        have Rfg_Sgh : ∃ (d1 d3: D) (g: d1 ⟶ d3 ), R.rel_morph f g ∧ S.rel_morph g h   := by
          simp [Relator.comp, relo_morph_comp] at RSfh
          obtain ⟨data⟩ := RSfh





      | @comp  c1 c2 e1 e2 f h _ T f j f1 f2 j1 j2 ffEqf jjEqj f1j1 f2j2 => sorry



-- --- Associativity of Composition---
-- -- First, let's prove associativity of ordinary relation composition (for objects)
-- theorem relComp_assoc {α β γ δ} (R : α → β → Prop) (S : β → γ → Prop) (T : γ → δ → Prop) :
--   ∀ a d, relComp (relComp R S) T a d ↔ relComp R (relComp S T) a d := by
--   intro a d
--   simp [relComp]
--   constructor
--   · intro h
--     -- If we have intermediate objects b and c
--     obtain ⟨c, ⟨b, Rab, Sbc⟩, Tcd⟩ := h
--     -- Rearrange to show existence in the other order
--     use b, Rab, c, Sbc, Tcd
--   · intro h
--     -- If we have intermediate objects b and c
--     obtain ⟨b, Rab, c, Sbc, Tcd⟩ := h
--     -- Rearrange to show existence in the other order
--     use c, ⟨b, Rab, Sbc⟩, Tcd


-- theorem Relator.comp_assoc {C D E I} [Category C] [Category D] [Category E] [Category I]
--     (R : Relator C D) (S : Relator D E) (T : Relator E I) : (R.comp S).comp T = R.comp (S.comp T) := by
--     rename_i catC catD catE catI
--     simp [comp]
--     constructor
--     · have h := relComp_assoc R.rel_ob S.rel_ob T.rel_ob
--       ext c1 i1 : 3
--       simp_all only [relComp]
--     · simp [relo_morph_comp]
--       ext c1 c2 i1 i2 f1 k1
--       constructor
--       · intro h
--         obtain ⟨ data⟩ := h
--       -- We need to prove by induction on the data structure
--         induction data with
--         | base  hProp  =>
--           rename_i c3 c4 i3 i4 f2 k2
--           -- Get the intermediate morphism in E
--           obtain ⟨e1, e2, h1, rs_f2h1, t_h1k2⟩ := hProp
--           -- Unpack the RS relation
--           simp at rs_f2h1 t_h1k2
--           obtain ⟨rs_data⟩ := rs_f2h1
--           sorry
--         | comp R S f g f1 f2 g1 g2 eq1 eq2 rs_data1 rs_data2 ih1 ih2 => sorry
--               -- This is the case where RS relation is built from smaller parts
--               -- We need to recurse on both parts
--       · sorry




-- To use this to make a category, we define:
-- def RelatorCategory : Category Type where
--   -- Objects are categories
--   Hom C D := Relator C D  -- For categories C and D
--   id C := sorry  -- Identity relator
--   comp := Relator.comp
--   id_comp := sorry
--   comp_id := sorry
--   assoc C D E F R S T := Relator.comp_assoc R S T


-- @[match_pattern]
-- inductive ReloCompCandidate {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]  {E : Type u''} [Category.{v''} E]  :
--     ∀ (R: Relator C D) (S: Relator D E){c1 c2 : C} {e1 e2 : E}, (c1 ⟶ c2) → (e1 ⟶ e2) → Type (max u u' u'' v v' v'')
-- | direct  {c1 c2 : C} {e1 e2 : E}  (R: Relator C D) (S: Relator D E) (f: c1 ⟶ c2) (h: e1 ⟶ e2) : ReloCompCandidate R S f h
-- | indirect  {c1 c3 : C} {e1 e3 : E}  (R: Relator C D) (S: Relator D E) (f: c1 ⟶ c3) (h: e1 ⟶ e3) {c2: C} {e2:E} (f1: c1 ⟶ c2 )(f2: c2 ⟶ c3) (h1: e1 ⟶ e2 )(h2: e2 ⟶ e3)(ffEqf: f1≫f2 = f )(hhEqh: h1≫h2 = h) (f1h1: ReloCompCandidate R S f1 h1) (f2h2: ReloCompCandidate R S f2 h2) : ReloCompCandidate R S f h



-- def ReloCompCandidate.eval  {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E] {R: Relator C D} {S: Relator D E}
--     {c1 c2 : C} {e1 e2 : E} (fh: ReloCompCandidate R S f h) : (f: c1 ⟶ c2) →  (h: e1 ⟶ e2) → Prop :=
--       :=
-- match fh with
-- | direct R S f h => preComp R S f h
-- | indirect R S f h _ _ _ _  ffEqf hhEqh f1h1  f2h2 => eval f1h1 ∧ eval f2h2

-- @[simp]
-- def  ReloCompCandidate.fst {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E] {R: Relator C D} {S: Relator D E} {c1 c2 : C} {e1 e2 : E} {f: c1 ⟶ c2} {h: e1 ⟶ e2}  (_: ReloCompCandidate R S f h) := f

-- @[simp]
-- def  ReloCompCandidate.snd {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E] {R: Relator C D} {S: Relator D E} {c1 c2 : C} {e1 e2 : E} {f: c1 ⟶ c2} {h: e1 ⟶ e2}  (_: ReloCompCandidate R S f h) := h



-- def rel_morph_comp {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E]  (R: Relator C D) (S: Relator D E) {c1 c3 : C} {e1 e3 : E} (f: c1 ⟶ c3) (h: e1 ⟶ e3)  :=
--     preComp R S f h ∨ (∃ (c2 : C) (e2: E) (f1: c1 ⟶ c2 )(f2: c2 ⟶ c3) (h1: e1 ⟶ e2 )(h2: e2 ⟶ e3),  f1≫f2 = f ∧  (h1≫h2) = h ∧  rel_morph_comp R S f1 h1 ∧ rel_morph_comp R S f2 h2)

-- def rel_morph_comp {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {E : Type u''} [Category.{v''} E]  (R: Relator C D) (S: Relator D E){X Y : C} {X' Y' : E} f h :=
--     let preComp {X Y : C} {X' Y' : E}(f: X ⟶ Y) (h: X' ⟶ Y') := (∃ (d d' :D) (g:d ⟶d' ), R.rel_morph f g ∧ S.rel_morph g h)
--     -- The definition below says that (f,h) ∈ R;S if either (f,h) ∈  R_morph;S_morph OR there exist pairs (f1,h1), (f2,h2) ∈ R_morph;S_morph such that f1;f2 = f and g1;g2 = g. The second disjunct ensures that pairs in R;S_morph are closed under composition.
--     preComp f h ∨ (∃ (W : C) (W': E) (f1: X ⟶ W )(f2: W ⟶ Y) (h1: X' ⟶ W' )(h2: W' ⟶ Y'),  f1≫f2 = f ∧  (h1≫h2) = h ∧  preComp f1 h1 ∧ preComp f2 h2)


  -- obj_id_iff (c : C) (e : E) := by
  --   constructor
  --   · intro h
  --     simp
  --     simp_all only [relComp]
  --     constructor
  --     · obtain ⟨d, Rcd, Sde⟩ := h
  --       use d
  --       use  d
  --       use (𝟙 d)
  --       have h1 := (R.obj_id_iff c d).mp Rcd
  --       have h2 := (S.obj_id_iff d e).mp Sde
  --       exact ⟨h1, h2⟩
  --   · intro h
  --     simp_all
  --     have rel_morph_compRS := h
  --     obtain ⟨d,d',g , Rids, Sids ⟩ := h
  --     have h1 := (R.obj_id_iff c d).mpr
  --     have h2 := (S.obj_id_iff d e).mpr
  --     have ⟨RSce, _ ⟩  := comp_object_closure rel_morph_compRS
  --     simp at RSce
  --     obtain ⟨d3, Rcd3, Sd3e⟩ := RSce
  --     · use d3
  --     · rename_i comp_factorizes
  --       simp at  comp_factorizes
  --       obtain ⟨c2,e2,f1,f2,f1f2EqIdc, h1, h2, h1h2EqIde, ⟨ d4,d5, g1, Rf1g1,  Sg1g2⟩ , d6, d7, g2, Rf2g2, Sg2h2⟩ :=  comp_factorizes
  --       have ⟨RSce, _ ⟩  := comp_object_closure rel_morph_compRS
  --       simp at RSce
  --       obtain ⟨d3, Rcd3, Sd3e⟩ := RSce
  --       use d3

-- theorem comp_closure {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
--   {E : Type u''} [Category.{v''} E]
--   {R : Relator C D} {S : Relator D E}
--   {c1 c2 c3 : C} {e1 e2 e3 : E}
--   {f₁ : c1 ⟶ c2} {f₂ : c2 ⟶ c3} {h₁ : e1 ⟶ e2} {h₂ : e2 ⟶ e3}
--   (RSf1h1 : rel_morph_comp R S f₁ h₁)
--   (RSf2h2 : rel_morph_comp R S f₂ h₂)
--   : rel_morph_comp R S (f₁ ≫ f₂) (h₁ ≫ h₂) := by
--   -- We choose the second disjunct of `rel_morph_comp R S (...) (...)`
--   -- i.e. "∃ W W' f1 f2, f1≫f2 = f₁≫f₂ ∧ ∃ x x₁, x≫x₁ = h₁≫h₂ ∧ …"
--   right
--   -- Supply W=c2, W'=e2, f1=f₁, f2=f₂
--   use c2, e2, f₁, f₂
--   constructor
--   · rfl
--   -- Now supply x = h₁, x₁ = h₂
--   use h₁, h₂
--   constructor
--   · rfl
--   -- Finally we must show:
--   --   (∃ d d' g, R.rel_morph f₁ g ∧ S.rel_morph g h₁) ∧
--   --   (∃ d d' g, R.rel_morph f₂ g ∧ S.rel_morph g h₂).
--   constructor
--   · -- Case analysis on `RSf1h1 : rel_morph_comp R S f₁ h₁`
--     cases RSf1h1 with
--     | inl baseCase =>
--       -- The “base” part already has the form we want
--       exact baseCase
--     | inr compCase =>
--       -- The factorization part also yields a "base" piece for f₁,h₁.
--       obtain ⟨W, W', f1, f2, rfl, rfl,
--         ⟨d, d', g, Rf1g, SgStuff⟩, d2, d3, g2, Rf2g2, Sg2Stuff⟩ := compCase
--       exact ⟨d, d', g, Rf1g, SgStuff⟩
--   · -- Similarly for `RSf2h2`
--     cases RSf2h2 with
--     | inl baseCase =>
--       exact baseCase
--     | inr compCase =>
--       obtain ⟨W, W', f1, f2, rfl, rfl,
--         ⟨d, d', g, Rf1g, SgStuff⟩, d2, d3, g2, Rf2g2, Sg2Stuff⟩ := compCase
--       exact ⟨d, d', g, Rf1g, SgStuff⟩





-- first to obj comp and morph comp separately

-- Then define relations based on those which add in compositions.









#check  Prod.map compRelation composeRelation


end CategoryTheory
