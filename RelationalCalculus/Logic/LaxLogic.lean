-- This should be moved to its own project.

import Mathlib.Tactic
universe u v

def Predicate (α : Type u)  :=  α -> Prop

inductive PLLFormula where
| prop (p: Prop)
| and (a: PLLFormula)(b: PLLFormula)
| or (a: PLLFormula)(b: PLLFormula)
| ifThen (antecedant: PLLFormula)(consequent: PLLFormula)
| falsePLL
| somehow (a: PLLFormula)

def PropositionalConstant := {F: PLLFormula // ∃ (p:Prop ), F =  PLLFormula.prop p }

-- We define negation as an abbreviation for implies false.
abbrev PLLFormula.notPLL (F: PLLFormula) : PLLFormula := ifThen F falsePLL

structure PLLModelComponents.{w} (World: Type w) where
  accessibility: (Preorder  World)
  modality: (Preorder World)
  fallible: Set World
  evaluate (p: PLLFormula) : Set World



abbrev PLLModelComponents.Rᵢ (M: PLLModelComponents World):= M.accessibility
abbrev PLLModelComponents.Rₘ (M: PLLModelComponents World):= M.modality
abbrev PLLModelComponents.F (M: PLLModelComponents World):= M.fallible
abbrev PLLModelComponents.V (M: PLLModelComponents World):= M.evaluate


structure PLLModelAxioms.{w} (M : PLLModelComponents.{w} World) where
  nonempty_worlds: Nonempty World
  modality_subrelation_accessibility: M.Rₘ.lt ≤ M.Rᵢ.lt
  fallible_hereditary  {w w': World} (h1: M.Rᵢ.lt w w') : w ∈  M.F → w' ∈ M.F
  evaluation_hereditary  {w w': World} {p: PLLFormula} (h1: M.Rᵢ.lt w w')  : w ∈ M.V p  →  w' ∈ M.V p
  fallible_evaluation (p: PLLFormula) :   M.F ⊆ M.V p

-- A model is a triple of the world type, the components and proofs of the axioms.
def PLLModel.{w} := Σ (World: Type w), Σ (M : PLLModelComponents.{w} World), PLLModelAxioms.{w} M

-- Define accessors
def PLLModel.WorldType (M: PLLModel) := M.1
abbrev PLLModel.W (M: PLLModel) := M.WorldType
def PLLModel.components (M: PLLModel) := M.2.1

abbrev PLLModel.Rᵢ (M: PLLModel):= M.components.accessibility
abbrev PLLModel.Rₘ (M: PLLModel):= M.components.modality
abbrev PLLModel.F (M: PLLModel ):= M.components.fallible
abbrev PLLModel.V (M: PLLModel):= M.components.evaluate

def PLLModel.axioms (M: PLLModel) := M.2.2
-- If needed add accessors for the axioms.



-- Definition 3.2 (Validity). Let C=(W, Rm, Ri , V, F) be a constraint model for
-- PLL. Given a formula M and w # W, M is valid at w in C, written C, w < M iff
-- v M is a propositional constant A and w # V(A);
-- v M is N7K and both C, w < N and C, w < K;
-- v M is N6K and C, w < N or C, w < K;
-- v M is true, or M is false and w # F;
-- v M is N#K and for all v # W such that w Ri v, C, v < N implies C, v < K;
-- v M is of form mN and for all v # W, w Ri v, there exists u # W with v Rm u
-- such that C, u < N.
-- A formula M is valid in C, written C < M, if for all w # W, M is valid at w in C;
-- M is valid, written < M, if M is valid in any constraint model C.


-- We want to do a match over cases.


structure LaxLogicAbstraction where
  constraint: Predicate α
  formula: PLLFormula
