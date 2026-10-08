module DASHI.Cognition.Teleodynamics.E8ExceptionalBranchingBridgeExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

import DASHI.Foundations.ExceptionalAlbertFreudenthalResidualExact as Exceptional

------------------------------------------------------------------------
-- DASHI synthesis from the standard E8 -> E6 x A2 and E8 -> E7 x A1
-- branchings, with the literal root-set counts independently checked by
-- scripts/check_e8_exceptional_branching.py.
--
-- The 27- and 56-sized root fibres are NOT identified with the existing
-- Albert27/Freudenthal56 carriers without an explicit action/intertwiner.
------------------------------------------------------------------------

record E8E6A2RootSplitReceipt : Set where
  constructor e8e6a2
  field
    e6RootCount : Nat
    a2RootCount : Nat
    positiveMixedCount : Nat
    negativeMixedCount : Nat
    positiveFibreCount : Nat
    negativeFibreCount : Nat
    fibresPerSign : Nat

open E8E6A2RootSplitReceipt public

canonicalE8E6A2RootSplitReceipt : E8E6A2RootSplitReceipt
canonicalE8E6A2RootSplitReceipt = e8e6a2 72 6 81 81 27 27 3

record E8E7A1RootSplitReceipt : Set where
  constructor e8e7a1
  field
    e7RootCount : Nat
    a1RootCount : Nat
    positiveMixed56 : Nat
    negativeMixed56 : Nat

open E8E7A1RootSplitReceipt public

canonicalE8E7A1RootSplitReceipt : E8E7A1RootSplitReceipt
canonicalE8E7A1RootSplitReceipt = e8e7a1 126 2 56 56

rootCountE6A2 : 240 ≡ 72 + 6 + (3 * 27) + (3 * 27)
rootCountE6A2 = refl

adjointCountE6A2 : 248 ≡ 78 + 8 + (3 * 27) + (3 * 27)
adjointCountE6A2 = refl

rootCountE7A1 : 240 ≡ 126 + 2 + 56 + 56
rootCountE7A1 = refl

adjointCountE7A1 : 248 ≡ 133 + 3 + 56 + 56
adjointCountE7A1 = refl

record ExceptionalCrossPollinationBoundary : Set where
  constructor exceptionalCrossPollinationBoundary
  field
    e6Root72SectorExecutable : Bool
    a2Root6SectorExecutable : Bool
    threeBy27MixedFibresExecutable : Bool
    e7Root126SectorExecutable : Bool
    a1Root2SectorExecutable : Bool
    two56MixedFibresExecutable : Bool
    existingAlbert27OwnerReused : Bool
    existingFreudenthal56OwnerReused : Bool
    rootFibre27IsAlbertRepresentationHere : Bool
    rootFibre56IsFreudenthalRepresentationHere : Bool
    branchingCountsCreateExceptionalAction : Bool

open ExceptionalCrossPollinationBoundary public

canonicalExceptionalCrossPollinationBoundary : ExceptionalCrossPollinationBoundary
canonicalExceptionalCrossPollinationBoundary =
  exceptionalCrossPollinationBoundary
    true true true true true true true true false false false

albertDimensionAgreement : Exceptional.albertDimension ≡ 27
albertDimensionAgreement = refl

freudenthalDimensionAgreement : Exceptional.freudenthalDimension ≡ 56
freudenthalDimensionAgreement = refl
