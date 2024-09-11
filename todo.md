
# Refactoring

[]Use Relation namespace in Core.lean
[]Define notation co-located with definitions of operations.
[]Use notation consistently
  []Core.lean
  []Order
  []Eq
  []Union
  []Intersection


-- Notation
  -- Document the notation and track the precedence


-- Other Theorems to Possibly Prove

--Pairs:
-- Prove that every relation is equal to a (possibly infinite) union of pairs. Not sure if my current union definition allows for infinite unions.

-- Prove that if S ⊆ R and S is non-empty then there is a composition T;R;T' = S such that T and T' are subrelations of Id

-- Prove demorgan dualities between union and intersection

-- Prove distributive laws from Tarski paper for union and intersection.

-- Prove that Types and Relations form a category.

-- Show that this category forms an allegoy with union.







-- TODO: Prove that the so-called "allegory" laws holds for relations.
-- https://en.wikipedia.org/wiki/Allegory_(mathematics)
-- Allegory laws for intersection
-- Prove, intersection is idempotent, associative, commutative
-- Prove, converse distributes over intersection
-- composition is semi-distributive over union
-- modularity law
  -- Questions:
    -- should complement distribute over union?
    -- Does complement form a second allegory structure?



-- def FirstOrderRelation (α : Type u) (arity: Nat) (coarity: Nat) :

-- Univesally quantified props
  -- Implicit free variables
--Existentially quantified props
  -- Compose with full at one end or the other to implicity existentially quantify
-- Not, complement
-- And, Intersection
-- Or, Union
-- Evaluate at constant
  -- Compose with pair constructor on left or right or both left and right.
-- The whole relation is interpreted as a proposition by asking if there are any pairs in it. If it is empty the associated proposition is false.
-- Arity and co-arity
  -- Cartesian product on the right of relation gives arity
  -- Cartesian product on the left of relation gives coarity
  -- We ignore different bracketings (we can have some cannonical bracketing from top to bottom)

-- Higher Order Logic
  -- Relation Types
  -- Base type of individuals
  -- Relations built inductively from relations on individuals
  -- Could have a version of the inductive type which only takes the base type as a type parameter. This way all higher order relations built on a given base type could live in the same type universe (I think)
  -- Use ⊕ and ⊗ instead of union and intersection for or and and.
