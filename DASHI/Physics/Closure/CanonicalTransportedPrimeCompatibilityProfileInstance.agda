module DASHI.Physics.Closure.CanonicalTransportedPrimeCompatibilityProfileInstance where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (_≤_)

open import MonsterOntos using (SSP)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.Hecke.ChamberToShiftWitnessBridge as CTSW

open import DASHI.Physics.Closure.PrimeCompatibilityProfile as PCP
open import DASHI.Physics.Closure.TransportedPrimeCompatibilityProfile as TPCP
open import DASHI.Physics.Closure.CanonicalChamberToShiftWitnessBridgeInstance as CCWI
  using
    ( CanonicalClosureCarrier
    ; canonicalShiftPrimeImage
    ; canonicalPrimeCompatibilityProfile
    ; closurePrimeEmbedding
    ; canonicalChamberToShiftWitnessBridge
    ; canonicalIllegalCount≤forcedStableCountHist
    )
open import DASHI.Physics.Constraints.ConcreteInstance as CI using (CR; CP; CC)

------------------------------------------------------------------------
-- Exercise the transported-profile constructor on the same tiny canonical
-- carrier. This shows that the generic "forget multiplicity, keep lane
-- presence" route really lands the same witness-level bridge on the current
-- canonical image, rather than only existing abstractly.

canonicalTransportedPrimeCompatibilityProfile :
  PCP.PrimeCompatibilityProfile CanonicalClosureCarrier
canonicalTransportedPrimeCompatibilityProfile =
  TPCP.transportedPrimeCompatibilityProfile canonicalShiftPrimeImage

canonicalTransportedPrimeEmbedding : CanonicalClosureCarrier → FactorVec
canonicalTransportedPrimeEmbedding =
  PCP.PrimeCompatibilityProfile.primeEmbedding
    canonicalTransportedPrimeCompatibilityProfile

canonicalTransportedPrimeEmbedding≡closurePrimeEmbedding :
  ∀ x →
  canonicalTransportedPrimeEmbedding x ≡ closurePrimeEmbedding x
canonicalTransportedPrimeEmbedding≡closurePrimeEmbedding CI.CR = refl
canonicalTransportedPrimeEmbedding≡closurePrimeEmbedding CI.CP = refl
canonicalTransportedPrimeEmbedding≡closurePrimeEmbedding CI.CC = refl

canonicalTransportedPrimeEmbedding≡closureNative :
  ∀ x →
  canonicalTransportedPrimeEmbedding x
    ≡
  PCP.PrimeCompatibilityProfile.primeEmbedding canonicalPrimeCompatibilityProfile x
canonicalTransportedPrimeEmbedding≡closureNative =
  canonicalTransportedPrimeEmbedding≡closurePrimeEmbedding

canonicalTransportedIllegalMask :
  CanonicalClosureCarrier → SSP → SSP → Bool
canonicalTransportedIllegalMask =
  PCP.PrimeCompatibilityProfile.illegalMask
    canonicalTransportedPrimeCompatibilityProfile

canonicalTransportedShiftWitness :
  CanonicalClosureCarrier → SSP → CTSW.ShiftWitness
canonicalTransportedShiftWitness =
  PCP.PrimeCompatibilityProfile.witness
    canonicalTransportedPrimeCompatibilityProfile

canonicalTransportedChamberToShiftWitnessBridge :
  CTSW.ChamberToShiftWitnessBridge CanonicalClosureCarrier
canonicalTransportedChamberToShiftWitnessBridge =
  PCP.PrimeCompatibilityProfile.witnessBridge
    canonicalTransportedPrimeCompatibilityProfile

canonicalTransportedIllegalCount≤forcedStableCountHist :
  ∀ x p →
  CTSW.illegalCount-chamber canonicalTransportedChamberToShiftWitnessBridge x p
    ≤
  CTSW.forcedStableCount-hist canonicalTransportedChamberToShiftWitnessBridge x p
canonicalTransportedIllegalCount≤forcedStableCountHist =
  CTSW.forcedStableTransfer canonicalTransportedChamberToShiftWitnessBridge

canonicalTransportedIllegalCount≤closureNative :
  ∀ x p →
  CTSW.illegalCount-chamber canonicalTransportedChamberToShiftWitnessBridge x p
    ≤
  CTSW.forcedStableCount-hist canonicalChamberToShiftWitnessBridge x p
canonicalTransportedIllegalCount≤closureNative x p
  rewrite canonicalTransportedPrimeEmbedding≡closurePrimeEmbedding x =
  canonicalIllegalCount≤forcedStableCountHist x p
