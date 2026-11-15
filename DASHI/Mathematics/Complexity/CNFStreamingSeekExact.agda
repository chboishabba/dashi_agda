module DASHI.Mathematics.Complexity.CNFStreamingSeekExact where

------------------------------------------------------------------------
-- RESIDUAL-INDEX STREAM CURSOR
--
-- `Seek index xs` returns either the element at index, or the residual index
-- remaining after xs is exhausted.  Residuals compose sections without first
-- computing section lengths.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed

------------------------------------------------------------------------
-- Generic seek.
------------------------------------------------------------------------

data SeekResult (A : Set) : Set where
  found : A → SeekResult A
  exhausted : Nat → SeekResult A

seekList : ∀ {A : Set} → Nat → List A → SeekResult A
seekList index [] = exhausted index
seekList zero (x ∷ xs) = found x
seekList (suc index) (x ∷ xs) = seekList index xs

continueSeek :
  ∀ {A : Set} →
  SeekResult A → List A → SeekResult A
continueSeek (found x) right = found x
continueSeek (exhausted index) right = seekList index right

seekAppendExact :
  ∀ {A : Set}
    (left right : List A)
    (index : Nat) →
  continueSeek (seekList index left) right
  ≡ seekList index (Placed.append left right)
seekAppendExact [] right index = refl
seekAppendExact (x ∷ xs) right zero = refl
seekAppendExact (x ∷ xs) right (suc index) =
  seekAppendExact xs right index

mapSeek :
  ∀ {A B : Set} →
  (A → B) → SeekResult A → SeekResult B
mapSeek f (found x) = found (f x)
mapSeek f (exhausted index) = exhausted index

mapList :
  ∀ {A B : Set} →
  (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

seekMapExact :
  ∀ {A B : Set}
    (f : A → B)
    (xs : List A)
    (index : Nat) →
  mapSeek f (seekList index xs)
  ≡ seekList index (mapList f xs)
seekMapExact f [] index = refl
seekMapExact f (x ∷ xs) zero = refl
seekMapExact f (x ∷ xs) (suc index) =
  seekMapExact f xs index

------------------------------------------------------------------------
-- Direct truth-table seek: accepted rows emit nothing; rejected rows emit one.
------------------------------------------------------------------------

seekRejectedRows :
  ∀ {n : Nat} →
  (CNF.Bits n → Bool) →
  List (CNF.Bits n) →
  Nat →
  SeekResult (CNF.Clause n)
seekRejectedRows predicate [] index = exhausted index
seekRejectedRows predicate (row ∷ rows) index
    with predicate row
... | true = seekRejectedRows predicate rows index
... | false
    with index
...   | zero = found (CNF.forbidClause row)
...   | suc remaining = seekRejectedRows predicate rows remaining

seekRejectedRowsExact :
  ∀ {n : Nat}
    (predicate : CNF.Bits n → Bool)
    (rows : List (CNF.Bits n))
    (index : Nat) →
  seekRejectedRows predicate rows index
  ≡ seekList index (CNF.compileRejectedRows predicate rows)
seekRejectedRowsExact predicate [] index = refl
seekRejectedRowsExact predicate (row ∷ rows) index
    with predicate row
... | true = seekRejectedRowsExact predicate rows index
... | false
    with index
...   | zero = refl
...   | suc remaining = seekRejectedRowsExact predicate rows remaining

------------------------------------------------------------------------
-- Direct seek through placed predicates; no compilePlaced/compilePlacedAll list.
------------------------------------------------------------------------

mutual
  seekPlacedAll :
    ∀ {local global : Nat} →
    List (Placed.PlacedPredicate local global) →
    Nat →
    SeekResult (CNF.Clause global)
  seekPlacedAll [] index = exhausted index
  seekPlacedAll {local} (placed ∷ rest) index =
    seekPlacedRows
      (Placed.rename placed)
      (Placed.predicate placed)
      (CNF.allBits local)
      rest
      index

  seekPlacedRows :
    ∀ {local global : Nat} →
    (Fin.Fin local → Fin.Fin global) →
    (CNF.Bits local → Bool) →
    List (CNF.Bits local) →
    List (Placed.PlacedPredicate local global) →
    Nat →
    SeekResult (CNF.Clause global)
  seekPlacedRows rename predicate [] rest index =
    seekPlacedAll rest index
  seekPlacedRows rename predicate (row ∷ rows) rest index
      with predicate row
  ... | true = seekPlacedRows rename predicate rows rest index
  ... | false
      with index
  ...   | zero =
    found (Rename.renameClause rename (CNF.forbidClause row))
  ...   | suc remaining =
    seekPlacedRows rename predicate rows rest remaining

mutual
  seekPlacedAllExact :
    ∀ {local global : Nat}
      (placed : List (Placed.PlacedPredicate local global))
      (index : Nat) →
    seekPlacedAll placed index
    ≡ seekList index (Placed.compilePlacedAll placed)
  seekPlacedAllExact [] index = refl
  seekPlacedAllExact {local} (placed ∷ rest) index =
    seekPlacedRowsExact
      (Placed.rename placed)
      (Placed.predicate placed)
      (CNF.allBits local)
      rest
      index

  seekPlacedRowsExact :
    ∀ {local global : Nat}
      (rename : Fin.Fin local → Fin.Fin global)
      (predicate : CNF.Bits local → Bool)
      (rows : List (CNF.Bits local))
      (rest : List (Placed.PlacedPredicate local global))
      (index : Nat) →
    seekPlacedRows rename predicate rows rest index
    ≡
    seekList index
      (Placed.append
        (Rename.renameCNF rename
          (CNF.compileRejectedRows predicate rows))
        (Placed.compilePlacedAll rest))
  seekPlacedRowsExact rename predicate [] rest index =
    seekPlacedAllExact rest index
  seekPlacedRowsExact rename predicate (row ∷ rows) rest index
      with predicate row
  ... | true =
    seekPlacedRowsExact rename predicate rows rest index
  ... | false
      with index
  ...   | zero = refl
  ...   | suc remaining =
    seekPlacedRowsExact rename predicate rows rest remaining

------------------------------------------------------------------------
-- `Rename.renameCNF` is exactly mapList renameClause.
------------------------------------------------------------------------

renameCNFAsMap :
  ∀ {local global : Nat}
    (rename : Fin.Fin local → Fin.Fin global)
    (formula : CNF.CNF local) →
  Rename.renameCNF rename formula
  ≡ mapList (Rename.renameClause rename) formula
renameCNFAsMap rename [] = refl
renameCNFAsMap rename (clause ∷ clauses)
  rewrite renameCNFAsMap rename clauses = refl

seekRenameCNFExact :
  ∀ {local global : Nat}
    (rename : Fin.Fin local → Fin.Fin global)
    (formula : CNF.CNF local)
    (index : Nat) →
  mapSeek (Rename.renameClause rename) (seekList index formula)
  ≡ seekList index (Rename.renameCNF rename formula)
seekRenameCNFExact rename formula index
  rewrite renameCNFAsMap rename formula =
  seekMapExact (Rename.renameClause rename) formula index

------------------------------------------------------------------------
-- This cursor is the compositional substrate for transition -> initial ->
-- accepting global Cook--Levin clause access.
------------------------------------------------------------------------
