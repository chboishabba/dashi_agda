module DASHI.Cognition.PNF.ContextualFractranPrimeContainmentExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Foundations.SSPPrimeLane369Refinement as Lane369
import DASHI.TrackedPrimes as Tracked

------------------------------------------------------------------------
-- The signed FRACTRAN atlas and older tracked-prime 369 refinement use
-- distinct typed prime carriers. Do not identify them by raw Nat equality.
------------------------------------------------------------------------

record SignedTrackedLaneBridge : Set where
  constructor signedTrackedLaneBridge
  field
    signedLane : Signed.SSPPrime
    trackedLane : Tracked.SSP
    arithmeticValueAgrees : Signed.primeValue signedLane ≡ Tracked.toNat trackedLane

open SignedTrackedLaneBridge public

record ContextualPrimeContainment (depth : Nat) : Set where
  constructor contextualPrimeContainment
  field
    contextualPrime : Signed.SSPPrime
    bridge : SignedTrackedLaneBridge
    sameSignedLane : signedLane bridge ≡ contextualPrime
    containing369Address : Lane369.SSPPrimeLane369Refinement depth
    sameTrackedLane :
      Lane369.primeLane containing369Address ≡ trackedLane bridge

open ContextualPrimeContainment public

record PrimeContainmentBoundary : Set where
  constructor primeContainmentBoundary
  field
    rawPrimeNumberAloneDeterminesSemanticGeometry : Bool
    signedAndTrackedPrimeCarriersDefinitionallySame : Bool
    explicitBridgeCanAttach369DepthAddress : Bool
    landingPrimeCanCarryContainingAddressMetadata : Bool

canonicalPrimeContainmentBoundary : PrimeContainmentBoundary
canonicalPrimeContainmentBoundary =
  primeContainmentBoundary false false true true
