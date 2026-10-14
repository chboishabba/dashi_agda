module DASHI.Mathematics.Complexity.CNFStreamingSeekCostExact where

------------------------------------------------------------------------
-- PREDICATE-EVALUATION COST FOR STREAMED CNF SEEK
--
-- The existing streaming seek functions are extensionally exact but their
-- recursion cost was previously implicit.  This owner instruments the placed
-- predicate search without constructing `compilePlacedAll`.
--
-- Cost currency here = local truth-table predicate evaluations.  List/control
-- bookkeeping is a later constant-factor finite-machine compilation cost.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _^_)
open import Data.Nat.Base using (_≤_)
open import Data.Product using (_×_; _,_)
import Data.Fin.Base as Fin
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed
import DASHI.Mathematics.Complexity.CNFStreamingSeekExact as Seek
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinSizeExact as Size

------------------------------------------------------------------------
-- Costed result wrapper.
------------------------------------------------------------------------

record CostedSeek (A : Set) : Set where
  constructor costed-seek
  field
    result : Seek.SeekResult A
    predicateWork : Nat

open CostedSeek public

------------------------------------------------------------------------
-- Direct rejected-row cursor: at most one predicate evaluation per source row.
------------------------------------------------------------------------

seekRejectedRowsCosted :
  ∀ {n : Nat} →
  (CNF.Bits n → Bool) →
  List (CNF.Bits n) →
  Nat →
  CostedSeek (CNF.Clause n)
seekRejectedRowsCosted predicate [] index =
  costed-seek (Seek.exhausted index) zero
seekRejectedRowsCosted predicate (row ∷ rows) index
  with predicate row
... | true
  with seekRejectedRowsCosted predicate rows index
... | costed-seek found work =
  costed-seek found (suc work)
seekRejectedRowsCosted predicate (row ∷ rows) index
  | false
  with index
... | zero =
  costed-seek (Seek.found (CNF.forbidClause row)) (suc zero)
... | suc remaining
  with seekRejectedRowsCosted predicate rows remaining
... | costed-seek found work =
  costed-seek found (suc work)

seekRejectedRowsCostedResultExact :
  ∀ {n : Nat}
    (predicate : CNF.Bits n → Bool)
    (rows : List (CNF.Bits n))
    (index : Nat) →
  result (seekRejectedRowsCosted predicate rows index)
  ≡ Seek.seekRejectedRows predicate rows index
seekRejectedRowsCostedResultExact predicate [] index = refl
seekRejectedRowsCostedResultExact predicate (row ∷ rows) index
  with predicate row
... | true
  with seekRejectedRowsCosted predicate rows index
     | seekRejectedRowsCostedResultExact predicate rows index
... | costed-seek found work | exact = exact
seekRejectedRowsCostedResultExact predicate (row ∷ rows) index
  | false
  with index
... | zero = refl
... | suc remaining
  with seekRejectedRowsCosted predicate rows remaining
     | seekRejectedRowsCostedResultExact predicate rows remaining
... | costed-seek found work | exact = exact

seekRejectedRowsWorkBound :
  ∀ {n : Nat}
    (predicate : CNF.Bits n → Bool)
    (rows : List (CNF.Bits n))
    (index : Nat) →
  predicateWork (seekRejectedRowsCosted predicate rows index)
  ≤ Size.listLength rows
seekRejectedRowsWorkBound predicate [] index = NatP.≤-refl _
seekRejectedRowsWorkBound predicate (row ∷ rows) index
  with predicate row
... | true
  with seekRejectedRowsCosted predicate rows index
     | seekRejectedRowsWorkBound predicate rows index
... | costed-seek found work | bound = NatP.s≤s bound
seekRejectedRowsWorkBound predicate (row ∷ rows) index
  | false
  with index
... | zero = NatP.s≤s NatP.z≤n
... | suc remaining
  with seekRejectedRowsCosted predicate rows remaining
     | seekRejectedRowsWorkBound predicate rows remaining
... | costed-seek found work | bound = NatP.s≤s bound

------------------------------------------------------------------------
-- Costed placed-predicate search.  No compiled CNF list is created.
------------------------------------------------------------------------

mutual
  seekPlacedAllCosted :
    ∀ {local global : Nat} →
    List (Placed.PlacedPredicate local global) →
    Nat →
    CostedSeek (CNF.Clause global)
  seekPlacedAllCosted [] index =
    costed-seek (Seek.exhausted index) zero
  seekPlacedAllCosted {local} (placed ∷ rest) index =
    seekPlacedRowsCosted
      (Placed.rename placed)
      (Placed.predicate placed)
      (CNF.allBits local)
      rest
      index

  seekPlacedRowsCosted :
    ∀ {local global : Nat} →
    (Fin.Fin local → Fin.Fin global) →
    (CNF.Bits local → Bool) →
    List (CNF.Bits local) →
    List (Placed.PlacedPredicate local global) →
    Nat →
    CostedSeek (CNF.Clause global)
  seekPlacedRowsCosted rename predicate [] rest index =
    seekPlacedAllCosted rest index
  seekPlacedRowsCosted rename predicate (row ∷ rows) rest index
    with predicate row
  ... | true
    with seekPlacedRowsCosted rename predicate rows rest index
  ... | costed-seek found work =
    costed-seek found (suc work)
  seekPlacedRowsCosted rename predicate (row ∷ rows) rest index
    | false
    with index
  ... | zero =
    costed-seek
      (Seek.found (Rename.renameClause rename (CNF.forbidClause row)))
      (suc zero)
  ... | suc remaining
    with seekPlacedRowsCosted rename predicate rows rest remaining
  ... | costed-seek found work =
    costed-seek found (suc work)

mutual
  seekPlacedAllCostedResultExact :
    ∀ {local global : Nat}
      (placed : List (Placed.PlacedPredicate local global))
      (index : Nat) →
    result (seekPlacedAllCosted placed index)
    ≡ Seek.seekPlacedAll placed index
  seekPlacedAllCostedResultExact [] index = refl
  seekPlacedAllCostedResultExact {local} (placed ∷ rest) index =
    seekPlacedRowsCostedResultExact
      (Placed.rename placed)
      (Placed.predicate placed)
      (CNF.allBits local)
      rest
      index

  seekPlacedRowsCostedResultExact :
    ∀ {local global : Nat}
      (rename : Fin.Fin local → Fin.Fin global)
      (predicate : CNF.Bits local → Bool)
      (rows : List (CNF.Bits local))
      (rest : List (Placed.PlacedPredicate local global))
      (index : Nat) →
    result (seekPlacedRowsCosted rename predicate rows rest index)
    ≡ Seek.seekPlacedRows rename predicate rows rest index
  seekPlacedRowsCostedResultExact rename predicate [] rest index =
    seekPlacedAllCostedResultExact rest index
  seekPlacedRowsCostedResultExact rename predicate (row ∷ rows) rest index
    with predicate row
  ... | true
    with seekPlacedRowsCosted rename predicate rows rest index
       | seekPlacedRowsCostedResultExact rename predicate rows rest index
  ... | costed-seek found work | exact = exact
  seekPlacedRowsCostedResultExact rename predicate (row ∷ rows) rest index
    | false
    with index
  ... | zero = refl
  ... | suc remaining
    with seekPlacedRowsCosted rename predicate rows rest remaining
       | seekPlacedRowsCostedResultExact
           rename predicate rows rest remaining
  ... | costed-seek found work | exact = exact

------------------------------------------------------------------------
-- Closed work bound: number of placed predicates times fixed local truth table.
------------------------------------------------------------------------

placedSeekBudget :
  ∀ {local global : Nat} →
  List (Placed.PlacedPredicate local global) → Nat
placedSeekBudget {local} placed =
  Size.listLength placed * (2 ^ local)

mutual
  seekPlacedAllWorkBound :
    ∀ {local global : Nat}
      (placed : List (Placed.PlacedPredicate local global))
      (index : Nat) →
    predicateWork (seekPlacedAllCosted placed index)
    ≤ placedSeekBudget placed
  seekPlacedAllWorkBound [] index = NatP.≤-refl _
  seekPlacedAllWorkBound {local} (placed ∷ rest) index
    rewrite Size.allBitsLength local =
    seekPlacedRowsWorkBound
      (Placed.rename placed)
      (Placed.predicate placed)
      (CNF.allBits local)
      rest
      index

  seekPlacedRowsWorkBound :
    ∀ {local global : Nat}
      (rename : Fin.Fin local → Fin.Fin global)
      (predicate : CNF.Bits local → Bool)
      (rows : List (CNF.Bits local))
      (rest : List (Placed.PlacedPredicate local global))
      (index : Nat) →
    predicateWork
      (seekPlacedRowsCosted rename predicate rows rest index)
    ≤ Size.listLength rows + placedSeekBudget rest
  seekPlacedRowsWorkBound rename predicate [] rest index =
    seekPlacedAllWorkBound rest index
  seekPlacedRowsWorkBound rename predicate (row ∷ rows) rest index
    with predicate row
  ... | true
    with seekPlacedRowsCosted rename predicate rows rest index
       | seekPlacedRowsWorkBound rename predicate rows rest index
  ... | costed-seek found work | bound = NatP.s≤s bound
  seekPlacedRowsWorkBound rename predicate (row ∷ rows) rest index
    | false
    with index
  ... | zero = NatP.s≤s NatP.z≤n
  ... | suc remaining
    with seekPlacedRowsCosted rename predicate rows rest remaining
       | seekPlacedRowsWorkBound rename predicate rows rest remaining
  ... | costed-seek found work | bound = NatP.s≤s bound

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- For fixed local width w, streamed placed-predicate seek evaluates at most
--
--   (# placed predicates) * 2^w
--
-- local rows.  `ConcreteTapeCookLevinSizeClosedExact` separately proves that
-- the global transition placed-predicate count is T*(cols-2), while the local
-- transition width is a machine constant.  Thus the dominant transition-clause
-- seek work is polynomial in the tableau dimensions for a fixed machine.
------------------------------------------------------------------------
