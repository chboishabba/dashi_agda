module DASHI.Core.RelationalHorizon369 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.SSP369JResolutionBifiltrationExact as Existing

------------------------------------------------------------------------
-- Canonical cumulative 3 / 6 / 9 relational horizon.
--
-- Reuse the repository's existing exact Triple carrier.  The three blocks may
-- have different coordinate types; 3/6/9 counts accumulated coordinate slots,
-- never candidate cardinality.
------------------------------------------------------------------------

data HorizonLevel : Set where
  H3 H6 H9 : HorizonLevel

Horizon3 : Set → Set
Horizon3 A = Existing.Triple A

record Horizon6 (A B : Set) : Set where
  constructor horizon6
  field
    first3 : Horizon3 A
    second3 : Existing.Triple B

open Horizon6 public

record Horizon9 (A B C : Set) : Set where
  constructor horizon9
  field
    first6 : Horizon6 A B
    third3 : Existing.Triple C

open Horizon9 public

project6to3 : ∀ {A B} → Horizon6 A B → Horizon3 A
project6to3 = first3

project9to6 : ∀ {A B C} → Horizon9 A B C → Horizon6 A B
project9to6 = first6

record RelationalHorizon369Boundary : Set where
  constructor relationalHorizon369Boundary
  field
    threeSixNineCountsBranches : Bool
    threeSixNineCountsBranchesIsFalse :
      threeSixNineCountsBranches ≡ false
    cumulativeBlocksReuseExistingTriple : Bool
    cumulativeBlocksReuseExistingTripleIsTrue :
      cumulativeBlocksReuseExistingTriple ≡ true

open RelationalHorizon369Boundary public

canonicalRelationalHorizon369Boundary : RelationalHorizon369Boundary
canonicalRelationalHorizon369Boundary =
  relationalHorizon369Boundary false refl true refl
