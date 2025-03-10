# Relational Calculus Library

This is an open source Lean 4 Library with data structures and theorems for working with the relational calculus.

The motivation of this is two-fold.

1. First as an educational resource for learning about the relational calculus theoretically.

2. Second as a formally verified foundation for implementing relational programming techniques in Lean or your own language of choice.

This is a work in progress. Please don't hesitate to reach out if you are interested in discussing the project or potentially getting involved.

## What it is not
I'm not a professional mathematician and this time the library isn't attempting to formalize research-level mathematics. It also isn't meant to be a practical tool for implementing relational programming techniques (at least not directly). Think of more as a formal specification of mathematical ideas that might be useful to inspire/guide the development of more practical libraries in various programming languages.

## What is the Relational Calculus?

The relational calculus is an algebraic theory and logic based on binary relations. It was pioneered by De Morgan, Peirce, Schroder, Tarski, and others. For a good historical and mathematical introduction see [Origins of the Calculus of Binary Relations by Vaughan Pratt](http://boole.stanford.edu/pub/ocbr.pdf).

## The Library

The documentation is just a sketch at this point. I'll work on filling it out over time.

### [Basic.lean](https://github.com/AviCraimer/relational-calculus-library-lean4/blob/main/RelationalCalculus/Basic.lean)
- Definition of `Relation` an inductive data type for terms of the relational calculus
- Definition of `eval` to provide a semantic domain and the ability to use it for computation.
- Definition of compositional operations on relations
- Basic simplification theorems for relation expressions
- Various other theorems

### [Order.lean](https://github.com/AviCraimer/relational-calculus-library-lean4/blob/main/RelationalCalculus/Order.lean)
- Definition of a $\leq$ relation based on inclusion under evaluation.
- Typeclass instances for Preorder

### [Eq.lean](https://github.com/AviCraimer/relational-calculus-library-lean4/blob/main/RelationalCalculus/Eq.lean)
- Defining equivalence between relatiions as R ≤ S ∧ S ≤ R
- Type class instance for Setoid (equivalence relation)
- Instance for HasEquiv type class
- Notation using R ≈ S
- Theorems to go back and forth from  R ≈ S to eval R = eval S

### [Quotient.lean](https://github.com/AviCraimer/relational-calculus-library-lean4/blob/main/RelationalCalculus/Quotient.lean)
- Definition of RelationQuotient as the type of relation expressions quotiented by equivalence class (≈)
- Definitions of lifted constructors for idR (identity relation) and comp (sequential composition).
- Theorems for identity composition and composition associativity (these are used to define the Category of Relations)

### [Category.lean](https://github.com/AviCraimer/relational-calculus-library-lean4/blob/main/RelationalCalculus/Category.lean)
- Definition of the category of relations (Rel) using RelationQuotient for the Hom type.

### [Union.lean](https://github.com/AviCraimer/relational-calculus-library-lean4/blob/main/RelationalCalculus/Union.lean)
- Defining `union` operation on relations using relational composition.
- Proof that `eval R ∪ S = eval R ∪ eval S`, i.e.,   evaluating this `union` is equal to evaluating set-theoretic union after evaluation.
- Properties of union: associativity, transitivity, commutativity.

### [Intersection.lean](https://github.com/AviCraimer/relational-calculus-library-lean4/blob/main/RelationalCalculus/Intersection.lean)
- Defining `intersection` operation on relations
- WIP
- Note: Most of these theorems should be derivable from `union` using the DeMorgan equivalence.

### [Logic.lean](https://github.com/AviCraimer/relational-calculus-library-lean4/blob/main/RelationalCalculus/Logic.lean)
- Defining Propositions as Relations
- Defining classical propositional connectives using relations
- Defining quantifiers using relations
- Defining sub-relation propositions relationally using linear implication
- Eventually I hope to prove equivalences of logic expressed in relations to ordinary predicate logic, but it's not there yet.


## Connections to Other Topics

### Connection with Formal Logic

Tarski in particular described an influential version of the calculus based on endo-relations. See his very readable [1941 paper](https://www.cl.cam.ac.uk/teaching/1011/Databases/Tarski_1941.pdf) for details. Tarski and others in the 20th Century to explore this calculus as an alternative to traditional logic based on sets and propositions.  One advantage of the calculus is that it eliminates the need for variable binding that is found in syntactic calculi such as the lambda calculus. Logical inference within the relational calculus can be accomplished entirely through simple substitution with no backtracking or variable name management.

However, an incompleteness result appeared to show that logic based on the relational calculus was incomplete relative to classical first-order logic. This result discouraged many from paying attention. However, recent work has demonstrated that full-first order relational logic is possible using an expanded set of primitive relations and operations. See [Diagrammatic Algebra of First Order Logic (2024)](https://arxiv.org/pdf/2401.07055).

One fascinating discovery is that the full calculus of relations provides one of the most natural interpretations of *linear logic*.

### Connection with Relational Databases

I'm not a database person myself so I don't know as much about this. However, apparently, foundational work in relational databases leading to query languages such as SQL were at least heavily inspired by The Calculus of Relations.


### Connection with Knowledge Representation

There seems to be a natural cognitive fit between binary relations and knowledge representation. Usefulness of structures such as knowledge graphs can naturally be modeled using binary relations. More complex structures, including higher-order networks can also be modeled with relations although in a somewhat less straightforward way.

### Connection with Logic Programming

Some logic programming languages implement a relational programming model. I don't now if any are explicitly based on the relational calculus.

