import Mathlib.Tactic
universe u v

namespace Utility

@[reducible]
def typeof {α : Sort u} (_:α) := α


--- VECT ---

-- I might remove this,  see:  Mathlib.Data.Vector
inductive Vect :  Type u -> Nat -> Type (u+1) :=
 | emptyV (α:Type u) : Vect α 0
 | consV {n : Nat } (a: α) (v: Vect α n): Vect α (n + 1)


def Vect.toList :  Vect α n → List α
  | emptyV α  => ([] : List α)
  | consV a v2 => a :: toList v2


instance [Repr α] : Repr (Vect α n) where
  reprPrec v _ :=
    let list := v.toList
    let listRepr := repr list
    let len := repr n
    s!"{listRepr} : Vect " ++ len

end Utility

namespace List
open Utility
def List.toVect : (l : List α) → Vect α l.length
  | [] => Vect.emptyV α
  | (h :: t) => Vect.consV h (toVect t)
end List
