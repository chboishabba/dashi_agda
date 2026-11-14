module DASHI.Mathematics.Complexity.CNFStreamingClauseLookupExact where

------------------------------------------------------------------------
-- RANDOM-ACCESS PLACED CNF LOOKUP WITHOUT MATERIALISING LOCAL OR GLOBAL CNFS
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed

lookupList : ∀ {A : Set} → Nat → List A → Maybe A
lookupList zero [] = nothing
lookupList zero (x ∷ xs) = just x
lookupList (suc n) [] = nothing
lookupList (suc n) (x ∷ xs) = lookupList n xs

lookupAppend :
  ∀ {A : Set} →
  List A → List A → Nat → Maybe A
lookupAppend [] right index = lookupList index right
lookupAppend (x ∷ xs) right zero = just x
lookupAppend (x ∷ xs) right (suc index) =
  lookupAppend xs right index

lookupAppendExact :
  ∀ {A : Set}
    (left right : List A)
    (index : Nat) →
  lookupAppend left right index
  ≡ lookupList index (Placed.append left right)
lookupAppendExact [] right index = refl
lookupAppendExact (x ∷ xs) right zero = refl
lookupAppendExact (x ∷ xs) right (suc index) =
  lookupAppendExact xs right index

------------------------------------------------------------------------
-- Direct truth-table selector: scan rows; decrement only on rejected rows.
------------------------------------------------------------------------

lookupRejectedRows :
  ∀ {n : Nat} →
  (CNF.Bits n → Bool) →
  List (CNF.Bits n) →
  Nat →
  Maybe (CNF.Clause n)
lookupRejectedRows predicate [] index = nothing
lookupRejectedRows predicate (row ∷ rows) index
    with predicate row
... | true = lookupRejectedRows predicate rows index
... | false
    with index
...   | zero = just (CNF.forbidClause row)
...   | suc rest = lookupRejectedRows predicate rows rest

lookupRejectedRowsExact :
  ∀ {n : Nat}
    (predicate : CNF.Bits n → Bool)
    (rows : List (CNF.Bits n))
    (index : Nat) →
  lookupRejectedRows predicate rows index
  ≡ lookupList index (CNF.compileRejectedRows predicate rows)
lookupRejectedRowsExact predicate [] index = refl
lookupRejectedRowsExact predicate (row ∷ rows) index
    with predicate row
... | true = lookupRejectedRowsExact predicate rows index
... | false
    with index
...   | zero = refl
...   | suc rest = lookupRejectedRowsExact predicate rows rest

lookupTruthTableClause :
  ∀ {n : Nat} →
  (CNF.Bits n → Bool) →
  Nat →
  Maybe (CNF.Clause n)
lookupTruthTableClause {n} predicate index =
  lookupRejectedRows predicate (CNF.allBits n) index

lookupTruthTableClauseExact :
  ∀ {n : Nat}
    (predicate : CNF.Bits n → Bool)
    (index : Nat) →
  lookupTruthTableClause predicate index
  ≡ lookupList index (CNF.truthTableCNF predicate)
lookupTruthTableClauseExact {n} predicate index =
  lookupRejectedRowsExact predicate (CNF.allBits n) index

------------------------------------------------------------------------
-- Direct selector across placed predicates and their local truth-table rows.
------------------------------------------------------------------------

mutual
  lookupPlacedAll :
    ∀ {local global : Nat} →
    List (Placed.PlacedPredicate local global) →
    Nat →
    Maybe (CNF.Clause global)
  lookupPlacedAll [] index = nothing
  lookupPlacedAll {local}
      (placed ∷ rest) index =
    lookupPlacedRows
      (Placed.rename placed)
      (Placed.predicate placed)
      (CNF.allBits local)
      rest
      index

  lookupPlacedRows :
    ∀ {local global : Nat} →
    (Fin.Fin local → Fin.Fin global) →
    (CNF.Bits local → Bool) →
    List (CNF.Bits local) →
    List (Placed.PlacedPredicate local global) →
    Nat →
    Maybe (CNF.Clause global)
  lookupPlacedRows rename predicate [] rest index =
    lookupPlacedAll rest index
  lookupPlacedRows rename predicate (row ∷ rows) rest index
      with predicate row
  ... | true =
    lookupPlacedRows rename predicate rows rest index
  ... | false
      with index
  ...   | zero =
    just (Rename.renameClause rename (CNF.forbidClause row))
  ...   | suc remaining =
    lookupPlacedRows rename predicate rows rest remaining

mutual
  lookupPlacedAllExact :
    ∀ {local global : Nat}
      (placed : List (Placed.PlacedPredicate local global))
      (index : Nat) →
    lookupPlacedAll placed index
    ≡ lookupList index (Placed.compilePlacedAll placed)
  lookupPlacedAllExact [] index = refl
  lookupPlacedAllExact {local}
      (placed ∷ rest) index =
    lookupPlacedRowsExact
      (Placed.rename placed)
      (Placed.predicate placed)
      (CNF.allBits local)
      rest
      index

  lookupPlacedRowsExact :
    ∀ {local global : Nat}
      (rename : Fin.Fin local → Fin.Fin global)
      (predicate : CNF.Bits local → Bool)
      (rows : List (CNF.Bits local))
      (rest : List (Placed.PlacedPredicate local global))
      (index : Nat) →
    lookupPlacedRows rename predicate rows rest index
    ≡
    lookupList index
      (Placed.append
        (Rename.renameCNF rename
          (CNF.compileRejectedRows predicate rows))
        (Placed.compilePlacedAll rest))
  lookupPlacedRowsExact rename predicate [] rest index =
    lookupPlacedAllExact rest index
  lookupPlacedRowsExact rename predicate (row ∷ rows) rest index
      with predicate row
  ... | true =
    lookupPlacedRowsExact rename predicate rows rest index
  ... | false
      with index
  ...   | zero = refl
  ...   | suc remaining =
    lookupPlacedRowsExact rename predicate rows rest remaining

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- For placed Cook--Levin constraints, requested-clause access now streams all
-- the way through canonical assignment enumeration.  It constructs only the
-- selected rejected row's forbid-clause, then renames that one clause.  Neither
-- the local truth-table CNF nor the tableau-wide compilePlacedAll CNF is an
-- executable intermediate.
------------------------------------------------------------------------
