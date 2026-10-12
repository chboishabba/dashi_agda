module DASHI.Physics.Plasma.Phase243PeriodicConsumerQuotientExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Physics.Plasma.PhaseRook270Exact as Rook
import DASHI.Physics.Plasma.Phase243OrbitQuotientExact as Q54
import DASHI.Physics.Plasma.Phase243TorusReparameterizationExact as Torus
import DASHI.Physics.Plasma.Phase243ConsumerDescentExact as PhaseDescent

------------------------------------------------------------------------
-- PERIODIC PHYSICAL REALIZATION -> CORE54 CONSUMER QUOTIENT
--
-- This is the physical-observer weld missing from the finite quotient alone.
-- A realization of Core243 is allowed to use an incidence-indexed torus
-- translation for global phase advance and one torus reflection for inversion.
-- If the declared observer is invariant under those reparameterizations, its
-- realized consumer is phase invariant.  The canonical consumer-descent owner
-- then proves explicit factorization through Core54.
--
-- The theorem is intentionally observer-relative.  Whole-period surface norms
-- and other reparameterization-invariant ideal-plasma observables can satisfy
-- it.  Port placement, coil supports, blanket/divertor geometry or other
-- engineering observers may break the symmetry and must provide their own
-- receipt before using the quotient.
------------------------------------------------------------------------

record PeriodicPhase243Realization
    (PhysicalState Observation : Set) : Set₁ where
  constructor periodic-phase243-realization
  field
    realize : Rook.Core243 → PhysicalState
    observe : PhysicalState → Observation

    translate : Torus.TorusThirdNinthShift → PhysicalState → PhysicalState
    reflect : PhysicalState → PhysicalState

    realizeAdvanceIntertwines : (x : Rook.Core243) →
      realize (Rook.advanceCore x)
      ≡ translate
          (Torus.canonicalAdvanceShift
            (Rook.incidenceClass x)
            (Rook.incidenceV x))
          (realize x)

    realizeInverseIntertwines : (x : Rook.Core243) →
      realize (Rook.inverseCore x) ≡ reflect (realize x)

    translationObservationInvariant :
      (shift : Torus.TorusThirdNinthShift) →
      (state : PhysicalState) →
      observe (translate shift state) ≡ observe state

    reflectionObservationInvariant :
      (state : PhysicalState) →
      observe (reflect state) ≡ observe state

    sameObjectRealizationReceipt : Set
    realizationReference : String

open PeriodicPhase243Realization public

realizedObservation :
  ∀ {PhysicalState Observation : Set} →
  PeriodicPhase243Realization PhysicalState Observation →
  Rook.Core243 → Observation
realizedObservation r x = observe r (realize r x)

realizedAdvanceInvariant :
  ∀ {PhysicalState Observation : Set} →
  (r : PeriodicPhase243Realization PhysicalState Observation) →
  (x : Rook.Core243) →
  realizedObservation r (Rook.advanceCore x)
  ≡ realizedObservation r x
realizedAdvanceInvariant r x =
  trans
    (cong (observe r) (realizeAdvanceIntertwines r x))
    (translationObservationInvariant r
      (Torus.canonicalAdvanceShift
        (Rook.incidenceClass x)
        (Rook.incidenceV x))
      (realize r x))

realizedInverseInvariant :
  ∀ {PhysicalState Observation : Set} →
  (r : PeriodicPhase243Realization PhysicalState Observation) →
  (x : Rook.Core243) →
  realizedObservation r (Rook.inverseCore x)
  ≡ realizedObservation r x
realizedInverseInvariant r x =
  trans
    (cong (observe r) (realizeInverseIntertwines r x))
    (reflectionObservationInvariant r (realize r x))

compiledPhaseInvariantConsumer :
  ∀ {PhysicalState Observation : Set} →
  PeriodicPhase243Realization PhysicalState Observation →
  PhaseDescent.PhaseInvariantConsumer Observation
compiledPhaseInvariantConsumer r =
  PhaseDescent.phase-invariant-consumer
    (realizedObservation r)
    (realizedAdvanceInvariant r)
    (realizedInverseInvariant r)
    (realizationReference r)

periodicRealizationCore54Sufficient :
  ∀ {PhysicalState Observation : Set} →
  (r : PeriodicPhase243Realization PhysicalState Observation) →
  Descent.ConsumerSufficient Q54.quotientCore (realizedObservation r)
periodicRealizationCore54Sufficient r =
  PhaseDescent.phaseInvariantConsumerIsCore54Sufficient
    (compiledPhaseInvariantConsumer r)

periodicRealizationFactorsThroughCore54 :
  ∀ {PhysicalState Observation : Set} →
  (r : PeriodicPhase243Realization PhysicalState Observation) →
  Descent.FactorsThrough Q54.quotientCore (realizedObservation r)
periodicRealizationFactorsThroughCore54 r =
  PhaseDescent.phaseInvariantConsumerFactorsThroughCore54
    (compiledPhaseInvariantConsumer r)

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record PeriodicPhase243ConsumerBoundary : Set where
  constructor periodic-phase243-consumer-boundary
  field
    periodicInvariantConsumerMayUse54Representatives : Bool
    periodicInvariantConsumerMayUse54RepresentativesIsTrue :
      periodicInvariantConsumerMayUse54Representatives ≡ true
    arbitraryEngineeringConsumerMayUse54Representatives : Bool
    arbitraryEngineeringConsumerMayUse54RepresentativesIsFalse :
      arbitraryEngineeringConsumerMayUse54Representatives ≡ false
    quotientIsConsumerRelative : Bool
    quotientIsConsumerRelativeIsTrue :
      quotientIsConsumerRelative ≡ true
    coilPlasmaSameObjectStillRequiredAfterQuotient : Bool
    coilPlasmaSameObjectStillRequiredAfterQuotientIsTrue :
      coilPlasmaSameObjectStillRequiredAfterQuotient ≡ true

canonicalPeriodicPhase243ConsumerBoundary : PeriodicPhase243ConsumerBoundary
canonicalPeriodicPhase243ConsumerBoundary =
  periodic-phase243-consumer-boundary
    true refl
    false refl
    true refl
    true refl

consumerCrossPollinationReference : String
consumerCrossPollinationReference =
  "Reuses DASHI.Core.ConsumerDescentMinimalObserverExact: observer sufficiency is consumer-relative; phase symmetry licenses Core54 only after the realized observer is invariant on each quotient fibre."
