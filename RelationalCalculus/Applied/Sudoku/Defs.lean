import Mathlib.Data.Finset.Basic
import Mathlib.Tactic


namespace Sudoku

def Value : Finset Nat := {1,2,3,4,5,6,7,8,9}

def v (n : Nat) (h : n ∈ Value := by first | decide ) : { x // x ∈ Value } := ⟨n, h⟩

-- instance : Coe Nat  { x // x ∈ Value }  where
--   coe n :=  toValue n

def vasdasd : Value := v 1

def OptionalValue := Option Value

structure Place where
  -- The 3 x 3 square numbered from upper left then left to right in three big rows
  sector: Value
  -- The row top to bottom
  row: Value
  -- The column left to right
  col: Value
  -- If the board position has a fixed value
  fixedValue: Option Value
  -- If fixed value is non-empty this must match.
  assignedValue:  Option Value
deriving Repr, DecidableEq

def Place.empty (sector: Value)(col: Value)(row: Value) := Place.mk sector col row none none


def one : Value := ⟨ 1, by decide ⟩
def two : Value := ⟨ 2, by decide ⟩
def three : Value := ⟨ 3, by decide ⟩
set_option diagnostics true
def sector1NoValues : List Place :=
let empty  := Place.empty one
[
  empty one one, empty one two, empty one three,
  empty two one, empty two two, empty two three,
  empty three one, empty three two, empty three three,
]

#check (· %· : Nat -> Nat -> Nat )
#eval 1 - (1 % 3)

def getSector (row: Value) (col: Value) :=
 let rEdge := row.val - (row.val % 3)
 let cEdge := col.val - (col.val % 3)
 match cEdge,rEdge with
 | 0, 0 => 1
 | 3, 0 => 2
 | 6, 0 => 3
 | 0, 3 => 4
 | 3, 3 => 5
 | 6, 3 => 6
 | 0, 6 => 7
 | 3, 6 => 8
 | 6, 6 => 9
 | _,_ => sorry

#eval getSector 1 1



def shiftCol (n: Nat)(p: Place) :=
let raw := p.col.val + n
match raw with
| m + 10   => p
| v => {p with col := ⟨raw, sorry ⟩ }




-- def getInitialPlace (sector: Value) (col: ) (n: Value) (l: List Place ) : List Place :=
-- match n.val with
-- | m + 1 =>



-- A valid {arg} assignment



end Sudoku
