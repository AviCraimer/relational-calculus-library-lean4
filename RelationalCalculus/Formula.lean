import Mathlib.Tactic
import Mathlib.Data.Finset.Basic

universe u v
namespace RFormula

inductive SetF
| atomic (symbol: String) : SetF
| product   : SetF  -> SetF   -> SetF
| coproduct : SetF  -> SetF   -> SetF
deriving DecidableEq

@[simp]
def SetF.symbols (S :SetF): Finset String :=
match S with
| atomic s => {s}
| product A B => A.symbols ∪ B.symbols
| coproduct A B => A.symbols ∪ B.symbols

#check Finset.mem_singleton

@[simp]
abbrev SetF.substitution (S: SetF) :=  S.symbols → Type u

@[simp]
abbrev ElF := SetF × String


@[simp]
def ElF.set (e: ElF) :=
match e with
| (A, _) => A

@[simp]
def ElF.elSym (e: ElF) :=
match e with
| (_, x) => x

@[simp]
abbrev ElF.substitution (Els: Finset ElF) :=  Els → Σ(α :Type u), α

instance : DecidableEq ElF := inferInstance

@[simp]
abbrev  RelAtomData := SetF × SetF × String

instance : DecidableEq RelAtomData := inferInstance

def RelAtomData.mk (A B: SetF) (sym:String): RelAtomData := (A,B,sym)

@[simp]
def RelAtomData.domain (R: RelAtomData) :=
match R with
| (A, _, _) => A

@[simp]
def RelAtomData.codomain (R: RelAtomData) :=
match R with
| (_, B, _) => B

@[simp]
def RelAtomData.symbol (R: RelAtomData) :=
match R with
| (_, _, s) => s


inductive RelF : (Dom : SetF ) → (Cod : SetF ) ->  Type
| atomic  (R: RelAtomData)  :  RelF R.domain R.codomain
| pair (e1 :ElF )(e2:ElF ): RelF e1.set e2.set
| comp (F: RelF A B)(G: RelF B C) : RelF A C
| converse (F: RelF A B) : RelF B A
| complement (F: RelF A B) : RelF A B
| full (A:SetF ) (B:SetF )  : RelF A B
| product  (F : RelF A B) (G : RelF C D) : RelF (SetF.product A C) (SetF.product B D)
| coproduct  (F : RelF A B) (G : RelF C D) : RelF (SetF.coproduct A C) (SetF.coproduct B D)
| copy (A:SetF) : RelF A (SetF.product A A)
| collapse (A:SetF) : RelF (SetF.coproduct A A) A
| first (A:SetF ) (B:SetF) : RelF (SetF.product A B) A
| second (A:SetF ) (B:SetF) : RelF (SetF.product A B) B
| left (A:SetF) (B:SetF) : RelF A  (SetF.coproduct A B)
| right (A:SetF ) (B:SetF) : RelF B (SetF.coproduct A B)
-- deriving DecidableEq

def RelF.isAtom (F: RelF A B) : Prop := ∃ (s:String), RelF.atomic (RelAtomData.mk A B s) = F

@[simp]
def RelF.domain  (_: RelF A B):SetF := A

variable (Z: RelF A B )


@[simp]
def RelF.codomain  (_: RelF A B):SetF := B

def RelF.sets {A B: SetF} (F:RelF A B): Finset SetF :=
match F with
|atomic R => {R.domain, R.codomain}
|pair e1 e2  => {e1.set, e2.set}
|comp G H => G.sets ∪ H.sets
|converse G => G.sets
|complement G => G.sets
|full A B  =>  {A,B}
|product G H => G.sets ∪ H.sets ∪ {(SetF.product G.domain H.domain), (SetF.product G.codomain H.codomain)}
|coproduct G H => G.sets ∪ H.sets ∪ {(SetF.coproduct G.domain H.domain), (SetF.coproduct G.codomain H.codomain)}
|copy A => {A, SetF.product A A}
|collapse A => {A,SetF.coproduct A A}
|first A B=> {A, B, SetF.product A B}
|second A B=> {A, B, SetF.product A B}
|left A B => {A, B, SetF.coproduct A B}
|right A B => {A, B,  SetF.coproduct A B}

def RelF.setSymbols {A B: SetF} (F:RelF A B): Finset String :=
  let setsList  := Finset.toList F.sets
  let symbolList := setsList.map (fun S => SetF.symbols S)
  symbolList.foldl (fun acc x => acc ∪ x) ∅


def RelF.els  {A B: SetF} (F:RelF A B): Finset ElF :=
match F with
|pair e1 e2  => {e1, e2}
|comp G H => G.els ∪ H.els
|converse G => G.els
|complement G =>  G.els
|product G H => G.els ∪ H.els
|coproduct G H => G.els ∪ H.els
| _ => {}

def RelF.relAtoms  {A B: SetF} (F:RelF A B): Finset RelAtomData :=
match F with
|atomic R => {R}
|comp G H => G.relAtoms ∪ H.relAtoms
|converse G => G.relAtoms
|complement G =>  G.relAtoms
|product G H => G.relAtoms ∪ H.relAtoms
|coproduct G H => G.relAtoms ∪ H.relAtoms
| _ => {}

@[simp]
def RelF.setSubstitution {A B: SetF} (F:RelF A B):  F.setSymbols -> Type u

-- TODO: I need an actual substitution for any set made from the set symbols. This will require some kind of inductive proof.

def RelF.elSubstitution {A B: SetF} (F:RelF A B) (setSub: F.setSubstitution) := (e: F.els) -> (setSub e.set)
