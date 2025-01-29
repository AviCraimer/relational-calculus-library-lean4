import RelationalCalculus.Basic
import RelationalCalculus.Order
import RelationalCalculus.Eq
import RelationalCalculus.Element
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

-- Here are some tools for defining finite relations
open Relation
namespace Relation

-- -- A finite set of explicit pairs
-- @[simp]
-- def FinRelSet (α β : Type u) := Finset (α × β)

-- Constructs a set of relational pairs from a given Finset
@[simp]
def finRelPairsFn { α β : Type u} [DecidableEq α ][DecidableEq β] (pairSet : Finset (α × β) ) : Pairs α β  := fun (a: α )(b:β ) =>
  let p :  α × β := ⟨a,b⟩
  (p ∈ pairSet )

structure FinRelation ( α β : Type u)  [DecidableEq α ][DecidableEq β] where
  pairSet : Finset (α × β)

def FinRelation.pairs { α β : Type u} [DecidableEq α ][DecidableEq β] (R: FinRelation α β )  :=  finRelPairsFn R.pairSet

def FinRelation.rel { α β : Type u} [DecidableEq α ][DecidableEq β]  [DecidableEq α ][DecidableEq β] (R: FinRelation α β )   := atomic R.pairs

lemma FinRelation.rel_eq_atomic_pairs [DecidableEq α ][DecidableEq β] (R: FinRelation α β ) : R.rel = atomic R.pairs := by rfl

def FinRelation.eval  { α β : Type u} [DecidableEq α ][DecidableEq β]   (R : FinRelation α β ) := R.pairs

@[simp]
theorem FinRelation.eval_eq_rel_eval { α β : Type u}   [DecidableEq α ][DecidableEq β]   (R : FinRelation α β ) : R.eval = R.rel.eval := by  rfl


#check  Finset.instInsert

def FinRelation.insert { α β : Type u}   [DecidableEq α ][DecidableEq β] (R : FinRelation α β)(a: α )(b: β ): FinRelation α  β :=
  let p :  α × β := ⟨a,b⟩
  match R with
  | mk pairSet =>
     let _insert : Insert (α×β) (Finset (α×β)) := Finset.instInsert

     let sdfsdf : Finset (α×β) := _insert p pairSet


     sorry









-- The subtype of finRelations
def FinRelation ( α β : Type u) := {R: Relation α β // ∃ (pairSet: Finset (α × β)), (finRelation pairSet) = R }

def FinRelation.insert  { α β : Type u} (R_: FinRelation α β ): FinRelation α β :=
  let R := R_.val
