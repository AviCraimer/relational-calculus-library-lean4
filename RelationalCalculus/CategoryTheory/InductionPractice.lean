import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic
universe  v

@[simp]
lemma comp_simp { α γ β  : Type u} {f1 : α → β} {f2 : β → γ} : f2 ∘ f1 = fun (a: α) => f2 (f1 a) := by rfl

inductive FunctionExpr :  (α γ : Type u)  → Type (u+1)
| base (α γ : Type u) (f : α → γ)
  : FunctionExpr α γ

| comp (α γ : Type u) {β : Type u} {f1 : α → β} {f2 : β → γ}
       (component1 : FunctionExpr α β )
       (component2 : FunctionExpr β γ ) : FunctionExpr α γ



-- inductive FunctionExpr : ∀ (α γ : Type u)(f: α → γ), Type (u+1)
-- | base  : FunctionExpr α γ  f
-- | comp  :∀ (α γ : Type u)(f: α → γ ), ∃(β: Type u) (f1 : α → β)(f2 : β → γ)
--        (component1 : FunctionExpr α β  f1) (component2 : FunctionExpr β γ  f2), (hEq: f2 ∘ f1 = f) FunctionExpr α γ f


rec def FunctionExpr.length {α γ : Type u} {f: α → γ  } (expr: FunctionExpr f): Nat :=
 match expr with
  | .base => 1
  | .comp c1 c2 => 1 + c1.length + c2.length




-- inductive Foo {α γ : Type u} : (f: α → γ) → Type (u+1) where
-- | base (f: α → γ) : Foo f
-- | comp {β : Type u} {f1: α → β} {f2: β → γ} (component1: Foo f1) (component2 : Foo f2) : Foo (f2 ∘ f1)

theorem bar {C : Type u} [Category.{v} C] {c1 c2 : C} (f: c1 ⟶ c2)(foo: Foo f) (h: f = f ): foo = foo  := by
  induction foo with
  | @base c1 c2 f1  =>


    -- have h : (c1 ⟶ c2) = (c3 ⟶ c4) := by rfl

    rfl
  | @comp c1 c2 f foo1 foo2 =>
    rfl
