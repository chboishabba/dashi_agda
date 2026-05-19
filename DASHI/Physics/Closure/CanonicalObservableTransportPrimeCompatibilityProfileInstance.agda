module DASHI.Physics.Closure.CanonicalObservableTransportPrimeCompatibilityProfileInstance where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (_≤_)

open import MonsterOntos using (SSP)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.Hecke.ChamberToShiftWitnessBridge as CTSW

open import DASHI.Physics.Closure.AbstractGaugeMatterBundle as AGMB
open import DASHI.Physics.Closure.PrimeCompatibilityProfile as PCP
open import DASHI.Physics.Closure.ObservableTransportPrimeCompatibilityProfile as OTPCP
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
  using (canonicalShiftHeckeState; shiftPrimeEmbedding)
open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CAGMI
  using
    ( canonicalAbstractGaugeMatterBundle
    ; canonicalObservableTransportWitness
    )
open import DASHI.Physics.Closure.CanonicalTransportedPrimeCompatibilityProfileInstance as CTPCPI
  using
    ( canonicalTransportedPrimeEmbedding
    ; canonicalTransportedIllegalCount≤forcedStableCountHist
    )
open import DASHI.Physics.Constraints.ConcreteInstance as CI using (CR; CP; CC)

------------------------------------------------------------------------
-- Exercise the bundle-level ObservableTransportWitness lift concretely on the
-- canonical abstract gauge/matter bundle carrier.

CanonicalBundleCarrier : Set
CanonicalBundleCarrier = AGMB.Carrier canonicalAbstractGaugeMatterBundle

canonicalObservableTransportPrimeImage : AGMB.TargetCarrier canonicalObservableTransportWitness → FactorVec
canonicalObservableTransportPrimeImage x =
  shiftPrimeEmbedding (canonicalShiftHeckeState x)

canonicalObservableTransportPrimeCompatibilityProfile :
  PCP.PrimeCompatibilityProfile CanonicalBundleCarrier
canonicalObservableTransportPrimeCompatibilityProfile =
  OTPCP.observableTransportPrimeCompatibilityProfile
    canonicalAbstractGaugeMatterBundle
    canonicalObservableTransportWitness
    canonicalObservableTransportPrimeImage

canonicalObservableTransportPrimeEmbedding :
  CanonicalBundleCarrier → FactorVec
canonicalObservableTransportPrimeEmbedding =
  PCP.PrimeCompatibilityProfile.primeEmbedding
    canonicalObservableTransportPrimeCompatibilityProfile

canonicalObservableTransportPrimeEmbedding≡transported :
  ∀ x →
  canonicalObservableTransportPrimeEmbedding x
    ≡
  canonicalTransportedPrimeEmbedding x
canonicalObservableTransportPrimeEmbedding≡transported CI.CR = refl
canonicalObservableTransportPrimeEmbedding≡transported CI.CP = refl
canonicalObservableTransportPrimeEmbedding≡transported CI.CC = refl

canonicalObservableTransportIllegalMask :
  CanonicalBundleCarrier → SSP → SSP → Bool
canonicalObservableTransportIllegalMask =
  PCP.PrimeCompatibilityProfile.illegalMask
    canonicalObservableTransportPrimeCompatibilityProfile

canonicalObservableTransportShiftWitness :
  CanonicalBundleCarrier → SSP → CTSW.ShiftWitness
canonicalObservableTransportShiftWitness =
  PCP.PrimeCompatibilityProfile.witness
    canonicalObservableTransportPrimeCompatibilityProfile

canonicalObservableTransportChamberToShiftWitnessBridge :
  CTSW.ChamberToShiftWitnessBridge CanonicalBundleCarrier
canonicalObservableTransportChamberToShiftWitnessBridge =
  PCP.PrimeCompatibilityProfile.witnessBridge
    canonicalObservableTransportPrimeCompatibilityProfile

canonicalObservableTransportIllegalCount≤forcedStableCountHist :
  ∀ x p →
  CTSW.illegalCount-chamber
    canonicalObservableTransportChamberToShiftWitnessBridge x p
    ≤
  CTSW.forcedStableCount-hist
    canonicalObservableTransportChamberToShiftWitnessBridge x p
canonicalObservableTransportIllegalCount≤forcedStableCountHist =
  CTSW.forcedStableTransfer
    canonicalObservableTransportChamberToShiftWitnessBridge

canonicalObservableTransportIllegalCount≤transported :
  ∀ x p →
  CTSW.illegalCount-chamber
    canonicalObservableTransportChamberToShiftWitnessBridge x p
    ≤
  CTSW.forcedStableCount-hist
    canonicalObservableTransportChamberToShiftWitnessBridge x p
canonicalObservableTransportIllegalCount≤transported x p
  rewrite canonicalObservableTransportPrimeEmbedding≡transported x =
  canonicalTransportedIllegalCount≤forcedStableCountHist x p
