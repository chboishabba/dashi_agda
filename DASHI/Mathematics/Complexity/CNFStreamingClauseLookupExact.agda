module DASHI.Mathematics.Complexity.CNFStreamingClauseLookupExact where

------------------------------------------------------------------------
-- RANDOM-ACCESS CNF LOOKUP WITHOUT MATERIALISING CONCATENATED GLOBAL TAILS
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
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
-- Continuation cursor through compilePlacedAll.
------------------------------------------------------------------------

mutual
  lookupPlacedAll :
    ∀ {local global : Nat} →
    List (Placed.PlacedPredicate local global) →
    Nat →
    Maybe (CNF.Clause global)
  lookupPlacedAll [] index = nothing
  lookupPlacedAll (placed ∷ rest) index =
    lookupPlacedChunk (Placed.compilePlaced placed) rest index

  lookupPlacedChunk :
    ∀ {local global : Nat} →
    CNF.CNF global →
    List (Placed.PlacedPredicate local global) →
    Nat →
    Maybe (CNF.Clause global)
  lookupPlacedChunk [] rest index =
    lookupPlacedAll rest index
  lookupPlacedChunk (clause ∷ clauses) rest zero =
    just clause
  lookupPlacedChunk (clause ∷ clauses) rest (suc index) =
    lookupPlacedChunk clauses rest index

mutual
  lookupPlacedAllExact :
    ∀ {local global : Nat}
      (placed : List (Placed.PlacedPredicate local global))
      (index : Nat) →
    lookupPlacedAll placed index
    ≡ lookupList index (Placed.compilePlacedAll placed)
  lookupPlacedAllExact [] index = refl
  lookupPlacedAllExact (placed ∷ rest) index =
    lookupPlacedChunkExact (Placed.compilePlaced placed) rest index

  lookupPlacedChunkExact :
    ∀ {local global : Nat}
      (current : CNF.CNF global)
      (rest : List (Placed.PlacedPredicate local global))
      (index : Nat) →
    lookupPlacedChunk current rest index
    ≡
    lookupList index
      (Placed.append current (Placed.compilePlacedAll rest))
  lookupPlacedChunkExact [] rest index =
    lookupPlacedAllExact rest index
  lookupPlacedChunkExact (clause ∷ clauses) rest zero = refl
  lookupPlacedChunkExact (clause ∷ clauses) rest (suc index) =
    lookupPlacedChunkExact clauses rest index

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- Global transition-clause access can now consume the explicit finite list of
-- placed `(time,column)` predicates and stream across their local CNF templates.
-- The remaining materialisation seam is inside ONE local `compilePlaced`
-- truth-table template, not the polynomial tableau-wide CNF.
------------------------------------------------------------------------
