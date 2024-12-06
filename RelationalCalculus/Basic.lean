import Mathlib.Tactic
set_option pp.coercions false

universe u v


-- This is an extensional (set-like) definition of a relation as a subset of the Cartesian product α × β. The goal of many theorems will be to relate the algebraic structure of relational expressions to the semantics based on subsets of pairs.
abbrev Relation.Pairs (α β : Type u) : Type u  := (a:α) → (b:β) → Prop

-- The Relation inductive type gives the syntactic composition structure of relations. This defines the fundamental objects to be manipulated by the relational calculus.
@[match_pattern]
inductive Relation  : (Dom : Type u) → (Cod : Type u) → Type (u+1)
-- atomic forms a relation directly from a set of pairs
| atomic  {α β : Type u} (f:Relation.Pairs α β)  :  Relation α β

-- pair forms a relation as a pair of two values. This is useful for forming higher-order relations from existing relations.
| pair {α β : Type u} (a : α) (b : β) : Relation α β

-- comp stands for composition, and it is the sequential composition operation, which is defined analogously to function composition.
| comp {α β γ : Type u} (R : Relation α β) (S :Relation β γ) : Relation α γ

-- converse is one of the involutions of relations, it reverses the direction of the pairs.
| converse {α β : Type u} (R : Relation α β) : Relation β α

-- complement is the other involution, it consists of the set theoretic complement of pairs relative to a given relation.
| complement {α β : Type u} (R : Relation α β) : Relation α β

-- full is the relation which is the full subset of the Cartersian product of domain and codomain. It's complement is an empty relation.
| full (α β : Type u) : Relation α β

-- product is a monoidal product in the category Rel. It corresponds to one of the conjunction operations in linear logic, usually represented as ⊗.
| product {α β γ δ : Type u} (R : Relation α β) (S : Relation γ δ) : Relation (α × γ) (β × δ)

-- This is the coproduct in the category Rel. It corresponds to one of the disjunction operations in linear logic, usually represented as ⊕. It is interpreted as a disjoint union of domain, codomain, and relational pairs.
| coproduct {α β γ δ : Type u} (R : Relation α β) (S : Relation γ δ) : Relation (Sum α γ ) (Sum β δ)

-- Copy is the diagonal relation, connecting each value in the domain to a pair of identical copies in the codomain. The converse of this is a "merge" relation that sents pairs of identicals to a single copy.
| copy (α : Type u) : Relation α (α × α)

-- Collapse is the categorical dual of copy (a.k.a. cocopy).  It relates every left and right values of a sum type α + α  to equal values in α. This allows us to collapse the disjoint sets of the sum type into a single set. Among other things, this operation allows us to define a union operation compositonally. The converse is a "split" relation that splits a single value into two parallel copies in the disjoint sets.
| collapse (α: Type u) : Relation (Sum α α) α

-- First is a projection relation from a pair in the domain to the first member of the pair. The converse inserts a value into all pairs where it occurs in first position.
| first (α β : Type u) : Relation (α × β) α

-- Second is a projection relation from a pair in the domain to the second member of the pair. The converse inserts a value into all pairs where it occurs in second position.
| second (α β : Type u) : Relation (α × β) β

-- Left is an injection relation from a value to itself in the left side of a sum type. The converse is a kind of first projection that works with Sum types.
| left (α β : Type u) : Relation α (Sum α β)

-- Right is an injection relation from a value to itself in the right side of a sum type. The converse is a kind of second projection that works with Sum types.
| right (α β : Type u) : Relation β  (Sum α β)



open Relation
namespace Relation

postfix:80 "ᵒ" => converse -- \^o (hat and then letter)
postfix:80 "⁻" => complement -- \^- (hat dash)
infixl:70 " ⊗ " => product -- \otimes
infixl:60 " ⊕ " => coproduct -- \oplus
infixl:40 " ▹ " => comp -- \trans

@[simp]
abbrev domain (_: Relation α β) := α

@[simp]
abbrev codomain (_: Relation α β) := β



-- *** Eval - Semantics for Relations ***
-- eval defines the semantic domain of the Relation inductive type. It allows us to prove that different syntactic Relation are equal under evaluation.
def eval (Rel : Relation α β) : Pairs α β :=
match Rel with
-- For atomic relations, we simply return the pair function
| atomic f => f

-- Pair relations consist of the single pair of elements used in their definition
| pair a b => fun (a': α ) (b': β) => a = a' ∧ b = b'

-- A sequential composition of relations yeilds pair if there exists a common element in the middle Codomain/Domain. Note that for relations which have the structure of a function (i.e., relations with the properties of totality and determinism) this definition specializes to the standard definition of function composition.
| R ▹ S => fun (a : R.domain) (c : S.codomain) =>
  ∃ (b : S.domain), Relation.eval R a b ∧ Relation.eval S b c

-- A full relation has all pairs so returns a constant True proposition.
| full α β => fun _ _ => True

-- Converse returns an evaluation with the order of the arguments switched.
| Rᵒ  => fun a b => (Relation.eval R b a)

-- Complement returns the negation of evaluated proposition for each pair.
-- TODO: Investigate why pattern matching isn't working with the notation R⁻
|  complement R  => fun a b => ¬(Relation.eval R a b)

-- Product returns true iff the first element of the domain is related by R to the first element of the codomain AND the second element of domain is related by S to the second element of the codomain.
| product R S => fun (a: (R ⊗ S).domain) (b: (R ⊗ S).codomain) => (Relation.eval R a.1 b.1) ∧ (Relation.eval S a.2 b.2)

-- Coproduct returns true iff a left element of the domain is related by R to a left element of the codomain OR a right element of the domain is related by S to the right element of the codomain.
| coproduct R S => fun (a: (R⊕S).domain) (b: ((R⊕S)).codomain) =>
  match a, b with
  | Sum.inl a', Sum.inl b' => Relation.eval R a' b'
  | Sum.inr a', Sum.inr b' => Relation.eval S a' b'
  | _, _ => False

| copy α => fun a (a1, a2) => a = a1 ∧ a = a2

| collapse α => fun (aa) a =>
  match aa with
  | Sum.inl a' => a' = a
  | Sum.inr a' => a' = a

-- First and second relate the first (second) elements of a pair in domain to itself in codomain.
| first α β  => fun pair a => pair.1 = a
| second α β => fun pair b => pair.2 = b

-- Left and right relate an element of the domain to the corresponding left (right) elements of the codomain.
| left α β => fun a ab =>
  match ab with
  | Sum.inl a' => a = a'
  | _ => False
| right α β => fun a ba =>
  match ba with
  | Sum.inr a' => a = a'
  | _ => False


-- Expresses the evaluation function as a relation
def evalRel {α β : Type u} : Relation (Relation α β) (PLift (Pairs α β)) :=
  atomic fun (R : Relation α β) (f: PLift (Pairs α β) ) =>
    let evaluatedR := PLift.up (eval R)
  evaluatedR = f

-- **DEFINED RELATION OPERATIONS** --

-- The converse complement of a relation is often refered to as the relative or linear negation of the relation. Note, that this is order invariant, i.e. complement converse = converse complemetn (proof below).
def negation (R : Relation α β) := R⁻ᵒ
abbrev neg (R : Relation α β) :=  R.negation
postfix: 80 "ᗮ" => Relation.negation -- \^bot

-- Double converse equals original relation
@[simp]
theorem double_converse (R : Relation α β) : eval (converse (converse R)) = eval R := by
  apply funext; intro a; apply funext; intro b
  simp [eval, converse]

-- Double complement equals original relation
@[simp]
theorem double_complement (R : Relation α β) : eval (complement (complement R)) = eval R := by
  apply funext; intro a; apply funext; intro b
  simp [eval, complement]

-- Double negation (converse complement) equals original relation
@[simp]
theorem double_neg (R : Relation α β) : eval (neg (neg R)) = eval R := by
  apply funext; intro a; apply funext; intro b
  simp [eval, neg,  complement, converse]

-- complement-converse equals converse-complement. We simply to the later.
@[simp]
theorem converse_complement_sym (R : Relation α β) : eval (complement (converse R)) =  eval (converse ( complement  R))  := by
  apply funext; intro b; apply funext; intro a;
  simp [eval]

-- Complement-converse simplifies to negation. This is really trival but it helps display the expressions in a more readable way.
@[simp]
theorem complement_converse_to_neg (R : Relation α β) : eval (complement (converse R)) = eval (neg R) := by
  apply funext; intro b; apply funext; intro a;
  simp [eval, neg]


-- Merge is the converse of copy
def merge (α) := (copy α)ᵒ

-- The identity relation is the composition of copy and merge
def idR (α : Type u) := (copy α)▹(merge α)

-- Proves evaluation of copy then merge equals identity pairs.
@[simp]
theorem eval_idR {α : Type u}: eval (copy α ▹ merge α) = fun (a b: α ) => a = b  := by
simp [merge, eval]

-- Split is the converse of collapse. It branches α into two disjoint copies relating each element x to both inl x and inr x.
def split  (α : Type u) := (collapse α)ᵒ

-- Proves evaluation of split then collapse is evalutes the same as idR
@[simp]
theorem eval_split_collapse_eq_idR {α : Type u}: eval (split α ▹ collapse α) = eval (Relation.idR α)  := by
simp [split, eval]

-- The complement of identity is a relation consisting of all pairs of elements that are not identical.
def nonId (α : Type u) := (idR α)⁻

-- Prove that taking the linear negation of IdR is the same as nonId
theorem nonId_neg_idR  {α : Type u}: eval (nonId α) = eval  ((idR α)ᗮ) := by
  simp [eval]
  ext x x_1 : 3
  constructor
  <;> intro h
  <;> apply Aesop.BuiltinRules.not_intro
  <;> intro a
  <;> subst a
  <;> simp_all only [not_true_eq_false]

-- We need to prove that idR is symetric on its arguments and use this.


-- nonId relates two elements iff,  they are not equal
theorem eval_nonId_iff {α : Type u} (a a': α ) : eval (nonId α) a a' ↔ a ≠ a' := by simp [nonId, eval]

--The (linear) negation of copy is a "different" relation that relates pairs in α × α of non-equal elements to every element in α. It relates equal elements (a,a) to every element not equal to a. This is useful for compositionally removing reflexive pairs from a relation.
def different (α: Type u) := (copy α)ᗮ

-- This is a notion from Peirce/Tarski of a second sequential composition operation that is the logical dual of ordinary composition. It replaces the  existential quantifier (∃) in the definition of composition with a universal quantifier (∀) and replaces conjunction (∧) with disjunction (∨). It can be defined by a De Morgan equivalence.
-- Also called "par"
def rSum {α β : Type u} (R : Relation α β) (S :Relation β γ) :=  (R⁻▹S⁻)⁻

infixl:40 " ✦ " => rSum -- shortcut: \st4

@[simp]
theorem rsum_notation_simp {R  : Relation α β} {S :Relation β γ} : (R ✦ S) =  (rSum R S) := by rfl

@[simp]
theorem eval_relative_comp  {R: Relation α β }{S :Relation β γ} : eval (rSum R S) = fun (a: α)(c: γ) => ∀(b: β), eval R a b ∨ eval S b c := by
simp [rSum, complement, eval]
funext a b
simp [eval]
constructor <;> intro h ;
  · simp [Classical.or_iff_not_imp_left]
    exact h
simp [Classical.or_iff_not_imp_left.symm]
exact h


-- In linear logic, ar (upside down &) is the DeMorgan dual of product.
-- TODO: Need to check the name, not sure if it's called par.
def par (R : Relation α β) (S : Relation γ δ) : Relation (α × γ) (β × δ) := (Rᗮ⊗Sᗮ)ᗮ

-- In linear logic, the operation with (&) is the DeMorgan dual of coproduct.
def withR (R : Relation α β) (S : Relation γ δ) := (Rᗮ⊕Sᗮ)ᗮ

-- An empty relation is the complement of the full relation.
def empty (α β : Type u) :=  (full α β)⁻


-- Converse distributes over composition
@[simp]
theorem converse_comp_dist (R : Relation α β) (S : Relation β γ) :
  eval (converse (comp R S)) = eval (comp (converse S) (converse R)) := by
  apply funext; intro c; apply funext; intro a
  simp [Relation.eval]
  constructor <;> exact fun ⟨b, hab, hbc⟩ => ⟨b, hbc, hab⟩


-- Converse distributes across product
@[simp]
theorem converse_product_dist (R : Relation α β) (S : Relation γ δ) :
  eval (converse (product R S)) = eval (product (converse R) (converse S)) := by
  apply funext; intro ⟨b, d⟩; apply funext; intro ⟨a, c⟩
  simp [Relation.eval, Relation.product, Relation.converse]

-- Complement distributes across product
@[simp]
theorem complement_product_dist (R : Relation α β) (S : Relation γ δ) :
  eval (complement (product R S)) = eval (par (complement R) (complement S)) := by
  apply funext; intro ⟨a, c⟩; apply funext; intro ⟨b, d⟩
  simp [Relation.eval]

-- Negation distribtes across product
@[simp]
theorem neg_product (R : Relation α β) (S : Relation γ δ) :
  eval (neg (product R S)) = eval (par (neg R) (neg S)) := by
  apply funext; intro ⟨a, c⟩; apply funext; intro ⟨b, d⟩
  simp [Relation.eval]

-- Converse distributes across coproduct
@[simp]
theorem converse_coproduct (R : Relation α β) (S : Relation γ δ) :
  eval (converse (coproduct R S)) = eval (coproduct (converse R) (converse S)) := by
  apply funext; intro ab; apply funext; intro cd
  cases ab <;> cases cd <;> simp [Relation.eval]

--  Complement distributes across coproduct
@[simp]
theorem complement_coproduct (R : Relation α β) (S : Relation γ δ) :
eval (complement (coproduct R S)) = eval (withR (complement R) (complement S)) := by
apply funext; intro ab; apply funext; intro cd
cases ab <;> cases cd <;> simp [Relation.eval]

-- Composition is associative.
@[simp]
theorem assoc_comp (R : Relation α β) (S : Relation β γ) (T : Relation γ δ) :
  eval (comp (comp R S) T) = eval (comp R (comp S T)) := by
  apply funext; intro a; apply funext; intro d
  simp [Relation.eval]
  constructor
  . intro ⟨c, ⟨b, hab, hbc⟩, hcd⟩
    exact ⟨b, hab, ⟨c, hbc, hcd⟩⟩
  . intro ⟨b, hab, ⟨c, hbc, hcd⟩⟩
    exact ⟨c, ⟨b, hab, hbc⟩, hcd⟩




abbrev EndoRelation (α: Type U) := Relation α α

end Relation



-- *** Odds and Ends (Very Rough WIP) ***
-- Helper for getArityType. Note that arity' is arity - 1.
def getProduct (α : Type u) (arity': Nat) : Type u :=
  match arity' with
    | n+1 => α × (getProduct α n)
    | _ => α

-- Returns PUnit for arity 0, returns α for arity 1, α × α for arity 2, etc.
def getArityType (α : Type u) (arity: Nat) : Type u :=
if arity == 0 then PUnit else getProduct α (arity-1)




-- theorem Relation.product_coproduct__dist (R : Relation α α) (S : Relation α α) (T : Relation α α) :
--   eval (product (coproduct R S) T) = eval (coproduct (product R T) (product S T)) := sorry

-- theorem Relation.coproduct_product_dist (R : Relation α β) (S : Relation γ δ) (T : Relation ε ζ) :
-- eval (product (coproduct R S) T) = eval (coproduct (product R T) (product S T))  := by sorry

--  Equiv.sumProdDistrib is the distributivity equivalence for Sum and Product types. We need to apply this so the types match on either side of the eqution.
-- (R⊕S)⊗T ≅ (R⊗T)⊕(S⊗T)
theorem Relation.coproduct_product_dist (R : Relation α β) (S : Relation γ δ) (T : Relation ε ζ) :
  eval (product (coproduct R S) T) =
    fun (a :(α ⊕ γ) × ε) (b : (β ⊕ δ) × ζ) =>
      let prodPlusProd := eval (coproduct (product R T) (product S T))
      let isoDomain := (Equiv.sumProdDistrib α γ ε)
      let isoCodomain := (Equiv.sumProdDistrib β δ ζ)
      prodPlusProd (isoDomain a) (isoCodomain b) := by
  apply funext; intro a; apply funext; intro b
  dsimp [Relation.eval, Equiv.sumProdDistrib]
  cases a.1 <;> cases b.1 <;> simp


-- -- T⊕(R⊗S) = (T⊕R) ⊗ (T⊕S)
-- theorem Relation.product_coproduct_dist (R : Relation α β) (S : Relation γ δ) (T : Relation ε ζ) :
