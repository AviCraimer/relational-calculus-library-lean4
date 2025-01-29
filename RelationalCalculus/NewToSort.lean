import RelationalCalculus.Basic
import RelationalCalculus.Order
import RelationalCalculus.Eq
import RelationalCalculus.Element
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic


-- NOTE: There is some good stuff in here but I need to organize it and figure out which is worth keeping.

open Relation


-- Combining Conditions -- this is exploratory! Not sure about any of it.

theorem inequality_oplus  {α β : Type u}( R S R' S': Relation α β) : (R⊕R') ≤ S⊕S' ↔ R ≤ S ∧ R' ≤ S' := by
simp
apply Iff.intro
· intro a
  obtain ⟨left , right⟩ := a
  constructor <;> intro a b Rab
  · have h2 := left a
    obtain ⟨left2, right2 ⟩ := h2
    have h3 := left2 b

  · sorry
· intro a
  obtain ⟨left, right⟩ := a
  constructor
  · intro a
    constructor
    · intro a_1 a_2
      sorry
    · intro b a_1
      exact a_1
  · intro b
    constructor
    · intro a a_1
      exact a_1
    · intro b_1 a
      sorry


-- theorem inequality_conjunction  {α β : Type u}( R S R' S': Relation α β) : R⊗R' ≤ S⊗S' ↔ R ≤ S ∨ R' ≤ S' := by
--   simp [eval]
--   constructor
--   · intro h
--     constructor
--     · intro a b Rab
--       have h1 := h a a b b Rab
--     · sorry

--   · sorry
  -- · intro h
  --   constructor
  --   · intro a b Rab
  --     have h2 := h a a b b
  --     simp [eval] at h2
  --     have h3 := h2 Rab

  --   · intro a_1 b a_2
  --     sorry
  -- · intro a a_1 b a_2 b_1 a_3
  --   obtain ⟨left, right⟩ := a
  --   sorry





-- CONGRUENCE THEOREMS


@[simp]
lemma coproduct_congr  {α β γ δ : Type u}{ R R': Relation α β} {S S': Relation γ δ} (hR: R ≈ R') (hS: S ≈ S') : (R⊕S)  ≈ (R'⊕S') := by
 simp [(· ≈ · ), eq, (· ≤ · ), eval]
 constructor <;>  constructor
 · intro a b Rab
   rwa [eq_to_eval hR.symm]
 · intro c d Scd
   rwa [eq_to_eval hS.symm]
 · intro a b Rab
   rwa [eq_to_eval hR]
 · intro c d Scd
   rwa [eq_to_eval hS]


@[simp]
lemma comp_congr_left {α β γ : Type u}{ R R': Relation α β} {S: Relation β  γ } (hR: R ≈ R') : (R▹S)  ≈ (R'▹S)  := by
 simp [(· ≈ · ), eq, (· ≤ · ), eval, domain]
 constructor <;> intro a c b Rab Sbc <;> use b
 · rw [eq_to_eval hR.symm]
   exact ⟨Rab, Sbc⟩
 · rw [eq_to_eval hR.symm] at Rab
   exact ⟨Rab, Sbc⟩

@[simp]
lemma comp_congr_right {α β γ : Type u}{ R: Relation α β} {S S': Relation β  γ } (hS: S ≈ S') : (R▹S)  ≈ (R▹S')  := by
 simp [(· ≈ · ), eq, (· ≤ · ), eval, domain]
 constructor <;> intro a c b Rab Sbc <;> use b
 · rw [eq_to_eval hS.symm]
   exact ⟨Rab, Sbc⟩
 · rw [eq_to_eval hS.symm] at Sbc
   exact ⟨Rab, Sbc⟩

def coprodFromProd {α β γ δ : Type u} (R: Relation (α × γ) (β × δ)) : Relation (Sum α  γ) (Sum β δ) :=  (first α γᵒ▹R▹first β δ) ⊕ ((second α γᵒ)▹R▹second β δ)

def prodFromCoprod {α β γ δ : Type u} (R: Relation (Sum α  γ) (Sum β δ)) :  Relation (α × γ) (β × δ) :=  (left α γ▹R▹left β δᵒ) ⊗ (right α γ▹R▹right β δᵒ)


-- We can only recover R if S is non-empty since otherwise, we have no elemetns in R⊗S.
theorem recover_first_of_prod  {α β γ δ : Type u} (R: Relation α β) (S: Relation γ δ) (hNE: isNonEmpty S) :  R ≈ (first α γᵒ ▹ (R⊗S) ▹ first β δ) := by
simp  [(· ≈ · ), eq, (· ≤ · ),  eval]
simp [isNonEmpty,(· ≤ · ), eval] at hNE


have hLeft : ∀ (a : α) (b : β), R.eval a b → R.eval a b ∧ ∃ x x_1, S.eval x_1 x := by
  intro a b Rab
  constructor
  · assumption
  · obtain ⟨c, h⟩ := hNE
    obtain ⟨d, h⟩ := h
    use d ; use c

have hRight : (∀ (a : α) (b : β), R.eval a b → ∀ (x : δ) (x_1 : γ), S.eval x_1 x → R.eval a b) := by
  intro a b Rab d c _ ; assumption

exact ⟨ hLeft, hRight ⟩



-- We can only recover S if R is non-empty since otherwise, we have no elemetns in R⊗S.
theorem recover_second_of_prod  {α β γ δ : Type u} (R: Relation α β) (S: Relation γ δ) (hNE: isNonEmpty R) :  S ≈ (second α γᵒ ▹ (R⊗S) ▹ second β δ)  := by
simp  [(· ≈ · ), eq, (· ≤ · ),  eval]
simp [isNonEmpty,(· ≤ · ), eval] at hNE
intro a b Sab;
obtain ⟨a', h⟩ := hNE
obtain ⟨b', h⟩ := h
constructor
· use b' ; use a'
· exact Sab


theorem recover_left_of_coprod  {α β γ δ : Type u} (R: Relation α β) (S: Relation γ δ) : R ≈  (left α γ ▹ R⊕S ▹ left β δᵒ)  := by
simp  [(· ≈ · ), eq, (· ≤ · ), prodFromCoprod, eval]

theorem recover_right_of_coprod  {α β γ δ : Type u} (R: Relation α β ) (S: Relation γ δ ) : S ≈ (right α γ ▹ R⊕S ▹ right β δᵒ) := by simp  [(· ≈ · ), eq, (· ≤ · ), prodFromCoprod, eval]


theorem coproduct_equiv_prod  {α β γ δ : Type u} (R: Relation α β ) (S: Relation γ δ )  : (prodFromCoprod (R⊕S)) ≈ (R⊗S) := by
  simp [prodFromCoprod]
  have h1 :=  recover_left_of_coprod R S
  have h2 :=  recover_right_of_coprod R S
  have h3 := product_congr h1 h2
  exact h3.symm

-- I might not need this
theorem atom_prod_coprod  {α β γ δ : Type u} {R: Relation (α × γ) (β × δ)} : eval (coprodFromProd R) =  (fun(v1: Sum α γ) => fun ( v2: Sum β δ ) =>
    match v1, v2 with
    | Sum.inl a, Sum.inl b => ∃ c' d', eval R (a, c') (b, d')
    | Sum.inr c, Sum.inr d => ∃ a' b', eval R (a', c) (b', d)
    | _,_ => False
)  := by
simp [coprodFromProd, eval]
ext x x_1 : 3
cases x with
| inl val =>
  cases x_1 with
  | inl val_1 =>
    simp_all only
    constructor <;>
    intro a <;> obtain ⟨d, c, h⟩ := a <;> use c <;> use d
  | inr val_2 => simp_all only
| inr val_1 =>
  cases x_1 with
  | inl val => simp_all only
  | inr val_2 =>
    simp_all only
    constructor <;> intro a
    <;>  obtain ⟨b, a, h⟩ := a
    <;>  use a <;> use b

-- I might not need this
theorem atom_coprod_prod  {α β γ δ : Type u} {R: Relation (Sum α γ) (Sum β δ)} : eval (prodFromCoprod R) =  (fun ((a,c):  α × γ) ((b,d): β × δ) =>
  (eval R (Sum.inl a) (Sum.inl b)) ∧ eval R (Sum.inr c) (Sum.inr d)) := by
  simp  [(· ≈ · ), eq, (· ≤ · ), prodFromCoprod, eval]




-- coprodFromProd will have R inl a inl b and R inr c inr d iff R has (a, b)(c,d)

theorem prod_imp_coprod_conjunction {α β γ δ : Type u} {R: Relation α β } {S: Relation γ δ }  : ∀ (a: α )(c : γ) (b : β ) (d: δ), ((R⊗S).eval (a,c) (b,d)) → (((coprodFromProd (R⊗S)).eval (Sum.inl a) (Sum.inl b)) ∧ ((coprodFromProd (R⊗S)).eval (Sum.inr c) (Sum.inr d)))  := by
 intro a c b d
 rw [atom_prod_coprod]
 simp [eval]
 intro Rab Scd
 constructor
 · constructor
   ·  exact Rab
   · use c ; use d
 · constructor
   · use a ; use b
   · exact Scd

theorem  coprod_conjunction_imp_prod {α β γ δ : Type u} {R: Relation α β } {S: Relation γ δ }  : ∀ (a: α )(c : γ) (b : β ) (d: δ),  (((coprodFromProd (R⊗S)).eval (Sum.inl a) (Sum.inl b)) ∧ ((coprodFromProd (R⊗S)).eval (Sum.inr c) (Sum.inr d))) → ((R⊗S).eval (a,c) (b,d)) := by
 intro a c b d
 rw [atom_prod_coprod]
 simp [eval]
 intro Rab c' d' _ a' b' _ Scd
 constructor <;> assumption


theorem prod_eq_coprod_conjunction  {α β γ δ : Type u} {R: Relation α β } {S: Relation γ δ }  : ∀ (a: α )(c : γ) (b : β ) (d: δ), ((R⊗S).eval (a,c) (b,d)) = (((coprodFromProd (R⊗S)).eval (Sum.inl a) (Sum.inl b)) ∧ ((coprodFromProd (R⊗S)).eval (Sum.inr c) (Sum.inr d)))  := by
 intro a b c d
 simp
 constructor
 · exact prod_imp_coprod_conjunction a b c d
 · exact  coprod_conjunction_imp_prod a b c d


-- A product can be converted to a coproduct and back again.
theorem product_inverse  {α β γ δ : Type u} {R: Relation α β } {S: Relation γ δ }  : R⊗S  ≈ prodFromCoprod (coprodFromProd (R⊗S))   := by
simp only [(· ≈ · ), eq, (· ≤ · )]
rw [atom_coprod_prod, atom_prod_coprod]
simp_all
constructor
· intro a c b d RS
  constructor
  · use c ; use d
  · use a ; use b
·   intro a c b d c' d'
    -- TODO: Modify prod_eq_coprod_conjunction so it works without applying explicit arguments. Maybe I need to make a c b d implicit arguments as well.
    have h := @prod_eq_coprod_conjunction α β γ δ R S a c' b d'
    rw [h ]
    simp [eval]
    intro Rab d3 c3 _ b3 a3 _ _ a4 b4 _ Scd
    constructor <;> assumption



-- Interesting. So I discovered that you can't recover the coproduct when one of the sides is empty.
theorem coproduct_inverse  {α β γ δ : Type u} {R: Relation α β } {S: Relation γ δ }   (hNER: isNonEmpty R)(hNES: isNonEmpty S): (R⊕S)  ≈ coprodFromProd (prodFromCoprod (R⊕S))   := by
  have h : prodFromCoprod (R ⊕ S) ≈ R ⊗ S := coproduct_equiv_prod R S
  have hFirst : (first α γᵒ ▹ prodFromCoprod (R ⊕ S) ▹ first β δ) ≈ (first α γᵒ ▹ R⊗S ▹ first β δ) := by
    have h4 : (first α γᵒ ▹ prodFromCoprod (R ⊕ S)) ≈ (first α γᵒ ▹ R⊗S) := by exact comp_congr_right h
    exact comp_congr_left h4

  have hSecond : (second α γᵒ ▹ prodFromCoprod (R ⊕ S) ▹ second β δ) ≈ (second α γᵒ ▹ R⊗S ▹ second β δ) := by
    have h4 : (second α γᵒ ▹ prodFromCoprod (R ⊕ S)) ≈ (second α γᵒ ▹ R⊗S) := by exact comp_congr_right h
    exact comp_congr_left h4
  simp only [coprodFromProd]
  have hEquiv := coproduct_congr hFirst hSecond
  apply symm
  apply (instSetoid.iseqv.trans hEquiv)


  have hCoprod : (R ⊕ S) ≈ (first α γᵒ ▹ R ⊗ S ▹ first β δ) ⊕ (second α γᵒ ▹ R ⊗ S ▹ second β δ) := by
    have hLeft : R ≈ (first α γᵒ ▹ R ⊗ S ▹ first β δ) := by
      exact recover_first_of_prod R S hNES
    have hRight : S ≈ (second α γᵒ ▹ R ⊗ S ▹ second β δ) := by
      exact recover_second_of_prod R S hNER
    exact coproduct_congr hLeft hRight
  apply (instSetoid.iseqv.trans hCoprod.symm)
  simp_all
  rfl
