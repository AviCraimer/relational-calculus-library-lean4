import RelationalCalculus.Basic
import RelationalCalculus.Order
import RelationalCalculus.Eq
import Mathlib.Tactic
open Relation

namespace Relation

-- A left residual candidate is any relation that solves the inequality (R▹X) ≤ S
-- NOTE: I could call this "residual" and call the other "coresidual"
def leftResidualCandidate {α β : Type u} (R S: Relation α β) :=  {X: Relation β  β | (R▹X) ≤ S }

--- R ▹ X ≤ S
-- Schroder equialences
-- R▹X ≤ S ≃ X ≤ R⊸S ≃ R ≤ S⟜X

-- Definitions of (Left??) Residual
-- R⊸S = Rᗮ ▶ S = (Rᵒ▹S⁻)⁻

-- Key thing to prove
-- R▹(R⊸S) ≤ S

-- A left residual is a left residual candidate that is greater or equal to all candidates.
def leftResiduals {α β : Type u} (R S: Relation α β) :=  {X: Relation β β | X ∈ (leftResidualCandidate R S) ∧ ∀ (Y: (leftResidualCandidate R S)), Y ≤ X }

-- All left residuals are equivalent under evaluation.
theorem leftResidualsEquiv {α β : Type u} (R S: Relation α β) :
    ∀ (X X': ↑(R.leftResiduals S)), (X ≈ X') := by
  intro ⟨X, hX⟩ ⟨X', hX'⟩
  constructor
  · have h_X : X ∈ leftResidualCandidate R S ∧
               ∀ (Y: leftResidualCandidate R S), Y ≤ X := hX
    have h_X' : X' ∈ leftResidualCandidate R S ∧
                ∀ (Y: leftResidualCandidate R S), Y ≤ X' := hX'
    have h_X_in_candidate : X ∈ R.leftResidualCandidate S := h_X.left
    exact h_X'.right ⟨X, h_X_in_candidate⟩
  · have h_X : X ∈ leftResidualCandidate R S ∧
               ∀ (Y: leftResidualCandidate R S), Y ≤ X := hX
    have h_X' : X' ∈ leftResidualCandidate R S ∧
                ∀ (Y: leftResidualCandidate R S), Y ≤ X' := hX'
    have h_X'_in_candidate : X' ∈ R.leftResidualCandidate S := h_X'.left
    exact h_X.right ⟨X', h_X'_in_candidate⟩

def linImp (R S : Relation α β): Relation β β  := (Rᵒ▹S⁻)⁻
abbrev leftResidual (R S : Relation α β) := linImp R S
def rightResidual (R S : Relation α β) := (S⁻▹Rᵒ)⁻

--NOTATION FOR Linear Implication
  infixr : 50 "⊸" => linImp -- \multi
  infixl : 50 "⟜" => rightResidual




-- The composition ((Rᵒ▹S⁻)⁻) which defines linear implication, gives us a left residual for R and S
theorem lin_imp_left_residual {α β : Type u} (R S: Relation α β): (R ⊸ S) ∈ (leftResiduals R S) := by
  let X := ((Rᵒ▹S⁻)⁻)
  -- First, show that X ∈ leftResidualCandidate R S
  have h1 : (R ▹ X) ≤ S := by
    -- Need to show that for all a b, if eval (R ▹ X) a b then eval S a b
    intros a b h_eval_R_X
    -- h_eval_R_X : eval (R ▹ X) a b
    -- So there exists c such that eval R a c ∧ eval X c b
    rcases h_eval_R_X with ⟨c, h_eval_Rac, h_eval_Xcb⟩
    -- eval X c b = ¬(eval (Rᵒ▹S⁻) c b)
    have h_eval_Xcb_eq : eval X c b = ¬(eval (Rᵒ▹S⁻) c b) := by simp [eval]
    -- So h_eval_Xcb = ¬(eval (Rᵒ▹S⁻) c b)
    rw [h_eval_Xcb_eq] at h_eval_Xcb
    -- Suppose for contradiction that ¬(eval S a b)
    by_contra h_not_Sab
    -- Now, consider that eval (Rᵒ▹S⁻) c b holds
    have h_eval_Ro_Sneg_c_b : eval (Rᵒ▹S⁻) c b := by
      -- Need to show ∃ d, eval Rᵒ c d ∧ eval S⁻ d b
      exists a
    contradiction
  -- So (R ▹ X) ≤ S, so X ∈ leftResidualCandidate R S
  have h_candidate : X ∈ leftResidualCandidate R S := h1
  -- Now, need to show that X is greater than any Y ∈ leftResidualCandidate R S
  have h2 : ∀ (Y : R.leftResidualCandidate S), Y ≤ X  := by
    intros Y  a b aYb
    -- Since Y ∈ leftResidualCandidate R S, (R ▹ Y) ≤ S
    have RY_less_S := Y.property.out

    -- Suppose for contradiction that ¬(eval X a b)
    have h_eval_Xab_eq : eval X a b = ¬(eval (Rᵒ▹S⁻) a b) := by simp [eval]
    by_contra h_not_Xab
    -- Then eval (Rᵒ▹S⁻) a b holds
    have h_eval_Ro_Sneg_ab : eval (Rᵒ▹S⁻) a b := by
      rw [h_eval_Xab_eq] at h_not_Xab
      exact not_not.mp h_not_Xab
    -- So there exists c, eval Rᵒ a c ∧ eval S⁻ c b
    rcases h_eval_Ro_Sneg_ab with ⟨c, h_eval_Ro_ac, h_eval_Sneg_cb⟩
    -- eval Rᵒ a c = eval R c a
    have h_eval_Rca : eval R c a := h_eval_Ro_ac
    -- Now, since eval Y a b, and eval R c a, we have eval (R ▹ Y) c b
    have h_eval_RY_c_b : eval (R ▹ Y) c b := by
      use a
    -- Since (R ▹ Y) ≤ S, eval S c b holds
    have h_eval_Scb : eval S c b := RY_less_S c b h_eval_RY_c_b
    -- Contradicts h_not_Scb
    contradiction
  -- Therefore, X ∈ leftResiduals R S
  exact ⟨h_candidate, h2⟩

-- TODO: Prove the analogous theorem for right residual.


theorem lin_imp_le {α β : Type u} (R S: Relation α β) : ((R ⊸ S) ≈ full β β) → R ≤ S := by
intro h
have h_neg_empty : eval (Rᵒ ▹ S⁻) = (fun _ _ => False) := by
  -- Since (R ⊸ S) ≈ full, its complement is empty.
  have h_comp : eval ((Rᵒ ▹ S⁻)) = (eval ((R ⊸ S)⁻)) := by
    simp [linImp, eval]
  rw [h_comp]
  have RSCompEval : (eval ((R ⊸ S)⁻)) = fun b1 b2 =>  ¬ (eval (full β β) b1 b2) := by
   -- Use the fact that (R ⊸ S) ≈ full
    rw [(Relation.eq_to_eval h).symm]
    simp [eval]
  rw [RSCompEval]
  simp [eval, full]

-- Now, to prove R ≤ S, we need to show that for all a b, R.eval a b → S.eval a b.
intros a b Rab
by_contra notSab  -- Assume ¬S.eval a b
-- Since R.eval a b and ¬S.eval a b, we have eval R a b ∧ ¬eval S a b
-- Consider eval (Rᵒ ▹ S⁻) b b
have counter : eval (Rᵒ ▹ S⁻) b b := by
  exists a
-- But from h_neg_empty, eval (Rᵒ ▹ S⁻) b b = False, which is a contradiction
rw [h_neg_empty] at counter
contradiction

-- Note: I don't think the inverse theorem follows. I tried proving it false, but could not complete the proof
-- theorem le_lin_imp {α β : Type u} (R S: Relation α β) : ¬ ((R ≤ S) → ((R ⊸ S)) ≈ full β β) := by
--  let R1Pairs := fun (a b: Bool) =>
--   match a, b with
--   | false, false => True
--   | _,_ => False
--  let R1 : Relation Bool Bool := atomic R1Pairs
--  let S1 := idR Bool
--  have h1 : R1 ≤ S1 := by
--    simp [(·≤·), eval]
--  have h3 : ¬ (∀  {T: Type (u+1)} {α β : T} (R S : Relation α β), (R ≤ S → (R⊸S) ≈ full β β)) := by
--    by_contra notH3
  --  have myCase := @notH3 (Type 1) (Bool:Type)  R1 S1
  -- I don't understand what is going on with the universe variables here. It seems like it won't infer u.


end Relation
