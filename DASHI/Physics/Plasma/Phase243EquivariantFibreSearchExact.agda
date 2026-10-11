module DASHI.Physics.Plasma.Phase243EquivariantFibreSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.PhaseRook270Exact as Rook
import DASHI.Physics.Plasma.Phase243OrbitQuotientExact as Q54
import DASHI.Physics.Plasma.Phase243PlasmaConsumerExact as Consumer
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce

------------------------------------------------------------------------
-- EQUIVARIANT PHYSICAL-FIBRE SEARCH OVER THE 54-CLASS QUOTIENT
--
-- The 243-state finite base may be reduced to 54 representatives only for a
-- physical consumer whose realized observable is invariant under the same
-- global C3 advance and inversion used by the quotient.  This file makes that
-- condition proof-relevant; no arbitrary consumer is silently quotiented.
------------------------------------------------------------------------

record PhaseEquivariantPhysicalConsumer
    (PhysicalState Observation : Set) : Set₁ where
  constructor phase-equivariant-physical-consumer
  field
    realize : Rook.Core243 → PhysicalState
    observe : PhysicalState → Observation
    advancePhysical : PhysicalState → PhysicalState
    inversePhysical : PhysicalState → PhysicalState
    realizeAdvanceIntertwines : (x : Rook.Core243) →
      realize (Rook.advanceCore x) ≡ advancePhysical (realize x)
    realizeInverseIntertwines : (x : Rook.Core243) →
      realize (Rook.inverseCore x) ≡ inversePhysical (realize x)
    observationAdvanceInvariant : (s : PhysicalState) →
      observe (advancePhysical s) ≡ observe s
    observationInverseInvariant : (s : PhysicalState) →
      observe (inversePhysical s) ≡ observe s
    consumerReference : String

open PhaseEquivariantPhysicalConsumer public

record Core54FibreCandidate
    (PhysicalState : Set)
    (population : ZeroBounce.DeclaredParticlePopulation) : Set₁ where
  constructor core54-fibre-candidate
  field
    quotientState : Q54.Core54
    representativeState : Rook.Core243
    representativeIsCanonical :
      representativeState ≡ Q54.representativeCore quotientState
    realization : Consumer.Phase243PhysicalRealization PhysicalState population
    realizationUsesRepresentative :
      Consumer.baseState realization ≡ representativeState
    hardNonAxisymmetricGateReceipt : Set
    quotientConsumerEquivarianceReceipt : Set
    candidateReference : String

open Core54FibreCandidate public

------------------------------------------------------------------------
-- Search accounting and executable replay receipt.
------------------------------------------------------------------------

rawCoreStateCount : Nat
rawCoreStateCount = 243

quotientRepresentativeCount : Nat
quotientRepresentativeCount = 54

sizeThreeOrbitCount : Nat
sizeThreeOrbitCount = 27

sizeSixOrbitCount : Nat
sizeSixOrbitCount = 27

orbitAccounting :
  sizeThreeOrbitCount * 3 + sizeSixOrbitCount * 6 ≡ rawCoreStateCount
orbitAccounting = refl

record Core54NumericalReplayReceipt : Set where
  constructor core54-numerical-replay-receipt
  field
    representativeCount : Nat
    representativeCountIs54 : representativeCount ≡ quotientRepresentativeCount
    nonAxisymmetricFloorPositive : Bool
    bestIncidenceClassIsSameFiniteHarmonicCrossChannel : Bool
    bestRelativePhaseClassAligned : Bool
    relativeBSpreadBelowOnePercent : Bool
    surfaceDivergenceAtNumericalFloor : Bool
    replayReference : String

canonicalCore54NumericalReplayReceipt : Core54NumericalReplayReceipt
canonicalCore54NumericalReplayReceipt =
  core54-numerical-replay-receipt
    quotientRepresentativeCount
    refl
    true
    true
    true
    true
    true
    "scripts/phase243_core54_physical_replay.py; low-resolution hard-nonaxis replay, not a free-boundary or orbit acceptance receipt."

record EquivariantFibreSearchBoundary : Set where
  constructor equivariant-fibre-search-boundary
  field
    everyPhysicalConsumerMayUse54Representatives : Bool
    everyPhysicalConsumerMayUse54RepresentativesIsFalse :
      everyPhysicalConsumerMayUse54Representatives ≡ false
    equivarianceRequiredBeforeQuotientSearch : Bool
    equivarianceRequiredBeforeQuotientSearchIsTrue :
      equivarianceRequiredBeforeQuotientSearch ≡ true
    numericalWinnerIsAcceptedMagnet : Bool
    numericalWinnerIsAcceptedMagnetIsFalse :
      numericalWinnerIsAcceptedMagnet ≡ false
    coilFreeBoundaryOrbitConsumersStillRequired : Bool
    coilFreeBoundaryOrbitConsumersStillRequiredIsTrue :
      coilFreeBoundaryOrbitConsumersStillRequired ≡ true

canonicalEquivariantFibreSearchBoundary : EquivariantFibreSearchBoundary
canonicalEquivariantFibreSearchBoundary =
  equivariant-fibre-search-boundary false refl true refl false refl true refl
