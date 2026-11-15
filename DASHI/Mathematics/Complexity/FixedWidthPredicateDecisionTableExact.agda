module DASHI.Mathematics.Complexity.FixedWidthPredicateDecisionTableExact where

------------------------------------------------------------------------
-- DEFUNCTIONALIZE A FIXED-WIDTH BOOL PREDICATE INTO FINITE ROW/DECISION DATA
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.CNFStreamingSeekExact as Seek

record DecisionRow (width : Nat) : Set where
  constructor decision-row
  field
    row : CNF.Bits width
    accepted : Bool

open DecisionRow public

freezePredicateRows :
  ∀ {width : Nat} →
  (CNF.Bits width → Bool) →
  List (CNF.Bits width) →
  List (DecisionRow width)
freezePredicateRows predicate [] = []
freezePredicateRows predicate (row ∷ rest) =
  decision-row row (predicate row)
  ∷ freezePredicateRows predicate rest

freezePredicate :
  ∀ {width : Nat} →
  (CNF.Bits width → Bool) →
  List (DecisionRow width)
freezePredicate {width} predicate =
  freezePredicateRows predicate (CNF.allBits width)

seekFrozenRejectedRows :
  ∀ {width : Nat} →
  List (DecisionRow width) →
  Nat →
  Seek.SeekResult (CNF.Clause width)
seekFrozenRejectedRows [] index = Seek.exhausted index
seekFrozenRejectedRows (decision-row row true ∷ rest) index =
  seekFrozenRejectedRows rest index
seekFrozenRejectedRows (decision-row row false ∷ rest) zero =
  Seek.found (CNF.forbidClause row)
seekFrozenRejectedRows (decision-row row false ∷ rest) (suc index) =
  seekFrozenRejectedRows rest index

seekFrozenRejectedRowsExact :
  ∀ {width : Nat}
    (predicate : CNF.Bits width → Bool)
    (rows : List (CNF.Bits width))
    (index : Nat) →
  seekFrozenRejectedRows
    (freezePredicateRows predicate rows)
    index
  ≡
  Seek.seekRejectedRows predicate rows index
seekFrozenRejectedRowsExact predicate [] index = refl
seekFrozenRejectedRowsExact predicate (row ∷ rest) index
  with predicate row
... | true =
  seekFrozenRejectedRowsExact predicate rest index
... | false
  with index
...   | zero = refl
...   | suc remaining =
  seekFrozenRejectedRowsExact predicate rest remaining

seekFrozenPredicateExact :
  ∀ {width : Nat}
    (predicate : CNF.Bits width → Bool)
    (index : Nat) →
  seekFrozenRejectedRows (freezePredicate predicate) index
  ≡
  Seek.seekRejectedRows predicate (CNF.allBits width) index
seekFrozenPredicateExact {width} predicate index =
  seekFrozenRejectedRowsExact
    predicate (CNF.allBits width) index

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ rest) = suc (listLength rest)

freezeRowsLengthExact :
  ∀ {width : Nat}
    (predicate : CNF.Bits width → Bool)
    (rows : List (CNF.Bits width)) →
  listLength (freezePredicateRows predicate rows)
  ≡ listLength rows
freezeRowsLengthExact predicate [] = refl
freezeRowsLengthExact predicate (row ∷ rest)
  rewrite freezeRowsLengthExact predicate rest = refl

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- For a fixed coded target, transition and acceptance local kernels may be
-- evaluated once at compile/specialisation time and represented at runtime by
-- finite row/Bool data.  Runtime rejected-row seek is exactly the old semantic
-- predicate seek but contains no higher-order predicate call.
------------------------------------------------------------------------
