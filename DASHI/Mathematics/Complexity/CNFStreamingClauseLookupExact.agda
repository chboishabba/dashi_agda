module DASHI.Mathematics.Complexity.CNFStreamingClauseLookupExact where

------------------------------------------------------------------------
-- RANDOM-ACCESS LOOKUP THROUGH CNF CONCATENATION WITHOUT BUILDING THE APPEND
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
-- Stream through a list of already-local placed predicates.
--
-- `lookupPlacedAll` may evaluate local truth-table templates as needed, but it
-- never constructs the concatenated global CNF returned by compilePlacedAll.
------------------------------------------------------------------------

lookupPlacedAll :
  ∀ {local global : Nat} →
  List (Placed.PlacedPredicate local global) →
  Nat →
  Maybe (CNF.Clause global)
lookupPlacedAll [] index = nothing
lookupPlacedAll (placed ∷ rest) index =
  lookupAppend
    (Placed.compilePlaced placed)
    (Placed.compilePlacedAll rest)
    index

lookupPlacedAllExact :
  ∀ {local global : Nat}
    (placed : List (Placed.PlacedPredicate local global))
    (index : Nat) →
  lookupPlacedAll placed index
  ≡ lookupList index (Placed.compilePlacedAll placed)
lookupPlacedAllExact [] index = refl
lookupPlacedAllExact (placed ∷ rest) index =
  lookupAppendExact
    (Placed.compilePlaced placed)
    (Placed.compilePlacedAll rest)
    index

------------------------------------------------------------------------
-- NOTE
--
-- This pays exact random access through the OUTER concatenation only.  It does
-- not yet avoid constructing `compilePlacedAll rest` as a value argument in the
-- right branch.  The next refinement is a continuation lookup that recurses
-- directly into `rest` once the selected index has passed the current local
-- template.  No claim of machine-time efficiency is promoted here yet.
------------------------------------------------------------------------
