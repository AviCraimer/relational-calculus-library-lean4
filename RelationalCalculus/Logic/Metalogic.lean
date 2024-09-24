-- This is heavily work in progress. Probably not worth looking at yet.
import RelationalCalculus.Logic.SimpTheorems
import RelationalCalculus.Basic
import RelationalCalculus.Utility
import RelationalCalculus.Order
import RelationalCalculus.Eq
import RelationalCalculus.Union
import RelationalCalculus.Intersection
import Mathlib.Tactic
import Init.SimpLemmas

open Utility
open Relation
open Logic
namespace Logic


-- inductive PredCalcSyntax where
-- | atom
-- | negation_
-- | conjunction
-- | disjunction
-- | implication
-- | universalQ
-- | existentialQ

-- inductive PredCalc : PredCalcSyntax -> Type (u+1) where
--   | atomPC {α : Type u} (h: α  -> Prop)(x: α) : PredCalc atom
--   | negPC (pInd: PredCalc _) : PredCalc negation_
--   | andPC (left: PredCalc _) (right: PredCalc _): PredCalc conjunction
--   | orPC (left: PredCalc _)(right: PredCalc _) : PredCalc disjunction
--   | impliesPC (left: PredCalc _)(right: PredCalc _) : PredCalc implication
--   | uniPC (α : Type u) (f: α  ->  PredCalc _) : PredCalc universalQ
--   | exsPC (α : Type u) (f: α  ->  PredCalc _) : PredCalc existentialQ



-- def PredCalc.predicate {α : Type u} := α → Prop



-- def PredCalc.eval  (syn : PredCalcSyntax) (P: (PredCalc _)) : Prop :=
-- match syn with
--  | atom  => P
--  | sorry
--  | negPC P => ¬(eval P)
--  | andPC P Q => eval P ∧  eval Q
--  | orPC P Q  => eval P ∨ eval Q
--  | impliesPC p Q => eval p → eval Q
--  | uniPC α  f => ∀(x: α), (eval (f x))
--  | exsPC α f => ∃(x: α), (eval (f x))

namespace Relation

-- A unary predicate is a selection endorelation. These correspond to subsets of α

-- structure PredicateR1 (α :Type u) where
--   R:  EndoRelation α
--   subset: proofR (R⊑(idR α))


-- theorem rel_calc_pred_calc_atom :    := sorry




-- NOTE: Stuff on higher arity predicates. I actually don't need this to show the correspondance with PredCalc since that uses only unary predicates.
-- structure PredicateR2 (α β :Type u) where
--   R: Relation α β

-- structure PredicateR3 (α β γ: Type u) where
--   R: Sum (Relation α (β × γ)) (Relation (β × γ) α )
-- -- Alternatively I can use ⊗ to combine a 1-place and 2-place relation.

-- structure predicate3' (α β γ: Type u) where
--   R1: PredicateR1 α
--   R2: PredicateR2 β γ

-- -- Can I generalize this to N-ary. Might need one type for even and one type for Odd.

-- inductive NaryPredicateR :  Nat -> (Type (u + 1)) :=
-- | prop (P: PropR) : NaryPredicateR 0
-- | one (R: EndoRelation α) (subset: proofR (R⊑(idR α))) : NaryPredicateR 1
-- | two (R: Relation α β) : NaryPredicateR 2
-- -- TODO: Need to add the relation argument here:
-- -- Maybe use a Vector for the types and then construct the relation type with a function.
-- | nary (n: Nat) (h: n > 2)   : NaryPredicateR n

end Relation

-- theorem propR_atomPI (P: PropR) : P ≈ TrueR ↔
