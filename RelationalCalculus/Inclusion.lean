
import RelationalCalculus.Basic
import RelationalCalculus.Order
import RelationalCalculus.Eq
import RelationalCalculus.Element
import Mathlib.Tactic

namespace Relation
open Relation

-- This should define the set of pairs in R which are not in S, that is it is R - S.
def subtract {α β :Type u} (R S: Relation α β ) := (copy α)▹(R ⊗ S⁻)▹(merge β)
infixl: 60 "⊖" => subtract -- \ominus

theorem subtract_eval {α β :Type u} {R S: Relation α β} : eval (R ⊖ S) = fun (a:α ) (b:β) => (R.eval a b) ∧ (¬S.eval a b) := by
  simp [eval, domain, codomain]
  funext a b
  simp
  constructor
  · intro h
    rcases h with ⟨a1,a2,⟨a_a1,a_a2⟩, Ra1b, nSa2b⟩
    constructor
    · rwa [a_a1.symm] at Ra1b
    · rwa [a_a2.symm] at nSa2b
  · intro h
    rcases h with ⟨Rab, nSab⟩
    use a, a

-- If R - S is empty then R is less than or equal to S
theorem rel_inclusion {α β :Type u} {R S: Relation α β} : (R ⊖ S ≈ empty α β) = (R ≤ S) := by
    simp [(·≈·), eq, (·≤·), eval, domain, codomain]

-- We prove that subtracting the difference between R and S form R gives a subrelation of S
theorem difference_subrelation {α β :Type u} (R S: Relation α β) : R⊖(R⊖S) ≤ S := by
 simp [(·≤·), eval, domain, codomain]
 intro a b Rab RabSab
 exact RabSab Rab

-- theorem sfdsdf  {α β :Type u} (R S: Relation α β) :∀ (a:α )(b:β), eval R-S a b →

-- theorem sdfd {α β :Type u} {R S T: Relation α β} {h1: R ≤ S}{h2: T ≤ S}:

theorem largest_subrelation {α β :Type u} {R S T: Relation α β} : T ≤ S → (T ≤ R⊖(R⊖S)) := by
  have RdiffSubS: R⊖(R⊖S) ≤ S := difference_subrelation R S
  simp [(·≤·), eval, domain, codomain]
  simp [(·≤·), (·⊖·), merge, eval, domain, codomain] at RdiffSubS
  intro TsubS
  have h1 : T ⊖ R ≈ empty α β := by
   simp [(·≈·), eq, (·≤·), eval, domain, codomain]
   intro a b
   by_contra nTR
   push_neg at nTR
   obtain ⟨Tab, nRab⟩ := nTR
   specialize TsubS a b
   specialize RdiffSubS a b
   have Sab := TsubS Tab
   -- I should be able to prove a contradition from Sab : S.eval a b, nRab : ¬R.eval a b ... actually not sure...



  intro h a b Tab
  constructor
  · sorry
  ·


def relInclusion {α β :Type u} (R S: Relation α β ) := (R ⊗ S⁻)⁻
infixl : 50 "⊑" => relInclusion

def disjunctiveRelInclusion {α β :Type u} (R S: Relation α β ) := (R⁻ ⊕ S)⁻




-- This appears not to hold if α or β are empty.
theorem le_then_inclusion {α β :Type u}  [hα: Nonempty α] [hβ :Nonempty β] (R S: Relation α β) : R ≤ S → isNonEmpty (R ⊑ S) := by
  simp [isNonEmpty, (·⊑·), relInclusion, (· ≤ · ), domain, codomain, eval]
  intro h
  by_cases hR : ∃ a b, R.eval a b
  · rcases hR with ⟨a, b, hRab⟩
    use a, a, b, b
    intro _
    exact h a b hRab
  · simp at hR
    let a := Classical.choice hα
    let b := Classical.choice hβ
    use a, a, b, b
    intro hRab
    exfalso
    exact hR a b hRab



theorem inclusion_then_le {α β :Type u}  [hα: Nonempty α] [hβ :Nonempty β] (R S: Relation α β) :  isNonEmpty (R ⊑ S) → R ≤ S  := by
  simp [isNonEmpty, (·⊑·), relInclusion, (· ≤ · ), domain, codomain, eval]
  -- Give friendly names to variables and re-order
  intro a1 a2 b1 b2 RS a b hab
  revert a b ; revert  a2 b2 ; revert a1  b1

  have hImp :  (∀ (a1 : α) (b1 : β) (a2 : α) (b2 : β), (R.eval a1 b1 → S.eval a2 b2)) → (∃ (a3: α)(b3: β), eval R a3 b3) → S ≈ (full α β)  := by
    intro h ex
    rcases ex with ⟨a3,b3, Ra3b3⟩
    specialize h a3 b3
    have isTrue : R.eval a3 b3 = True := by aesop
    rw [isTrue] at h
    simp at h
    simp [(· ≈·), eq,(· ≤ · ), eval ]
    exact h

  have hImpR :  (S ≈ (full α β)) →  (∀ (a1 : α) (b1 : β) (a2 : α) (b2 : β), (R.eval a1 b1 → S.eval a2 b2)) := by
   simp [(· ≈·), eq,(· ≤ · ), eval ]
   intro hSab a1 b1 a2 b2
   specialize hSab a2 b2
   aesop

  have converseHImpR : ¬ (∀ (a1 : α) (b1 : β) (a2 : α) (b2 : β), (R.eval a1 b1 → S.eval a2 b2)) → ¬ (S ≈ (full α β)) := by aesop

  by_cases RImpS : ∀ (a1 : α) (b1 : β) (a2 : α) (b2 : β), (R.eval a1 b1 → S.eval a2 b2)
  · by_cases  Rab:  ∃ (a3: α)(b3: β), eval R a3 b3
    · have Sfull := hImp RImpS Rab
      aesop
    · aesop
  · intro a1 b1 a2 b2
    have spec : ¬  R.eval a1 b1 → S.eval a2 b2 := by
      sorry
    sorry


    -- have SNotFull := converseHImpR RImpS
    -- push_neg at RImpS
    -- rcases RImpS with ⟨a1,b1,a2, b2,Ra1b1, notSa2b2⟩


  --  <;> by_cases  Rab:  ∃ (a3: α)(b3: β), eval R a3 b3
    -- ·

    -- have sddf := hImp ⟨RS, Rab⟩
