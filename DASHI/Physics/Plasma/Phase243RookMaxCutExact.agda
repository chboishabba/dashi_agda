module DASHI.Physics.Plasma.Phase243RookMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.PhaseRook270Exact as Rook
import DASHI.Physics.Plasma.PhaseCore243FiveTritExact as Bridge
import DASHI.Physics.Plasma.Phase243ActionIntertwinerExact as Action
import DASHI.Physics.Plasma.Phase243OrbitQuotientExact as Q54
import DASHI.Physics.Plasma.Phase243TorusReparameterizationExact as Torus
import DASHI.Physics.Plasma.Phase243ConsumerDescentExact as Descent
import DASHI.Physics.Plasma.Phase243PeriodicConsumerQuotientExact as Periodic
import DASHI.Physics.Plasma.Phase243EquivariantFibreSearchExact as Fibre
import DASHI.Physics.Plasma.Phase243PlasmaConsumerExact as Consumer

------------------------------------------------------------------------
-- CONSOLIDATED PHASE-243 MAX-CUT
--
-- Paid:
--   630 = 36 + 270 + 324 phase-resolved pair decomposition;
--   270 = 243 + 27 invariant rook split;
--   Core243 <-> FiveTrits total round-trip carrier recognition;
--   AxisBoundary27 <-> Ternary27Point total round-trip carrier recognition;
--   exact C3 advance / inversion action transport through both bijections;
--   exact Core243/(C3⋊C2) quotient to 54 incidence+relative-phase classes;
--   canonical action-word normalization of every Core243 state to its Core54
--     representative;
--   all 27 rook incidences admit an explicit torus translation implementing
--     simultaneous phase advance, while torus reflection implements inversion;
--   phase-invariant consumers are proved fibre-constant on Core54 and therefore
--     factor explicitly through the canonical sectioned quotient using the
--     repo's ConsumerDescentMinimalObserver machinery;
--   any periodic physical realization whose observer is invariant under those
--     translations/reflection compiles to the same Core54 factorization;
--   low-resolution hard-nonaxis 54-representative physical reconnaissance.
--
-- Open physical frontier:
--   the quotient is consumer-relative.  Ideal whole-period observables can use
--   it once their periodic realization receipt is supplied; arbitrary coil,
--   divertor, blanket, port/support or other engineering observers may break
--   the symmetry.  Surviving fibres still require same-object coil+plasma
--   free-boundary equilibrium, full orbit/FOW/EP consumers and same-chart
--   best-known comparison.
------------------------------------------------------------------------

record Phase243MaxCutStatus : Set where
  constructor phase243-max-cut-status
  field
    rook270CarrierConstructed : Bool
    rook270CarrierConstructedIsTrue : rook270CarrierConstructed ≡ true
    invariant243Plus27SplitPaid : Bool
    invariant243Plus27SplitPaidIsTrue : invariant243Plus27SplitPaid ≡ true
    fiveTritCarrierBijectionPaid : Bool
    fiveTritCarrierBijectionPaidIsTrue : fiveTritCarrierBijectionPaid ≡ true
    ternary27BoundaryBijectionPaid : Bool
    ternary27BoundaryBijectionPaidIsTrue : ternary27BoundaryBijectionPaid ≡ true
    phaseActionIntertwinerPaid : Bool
    phaseActionIntertwinerPaidIsTrue : phaseActionIntertwinerPaid ≡ true
    actionQuotient54Paid : Bool
    actionQuotient54PaidIsTrue : actionQuotient54Paid ≡ true
    incidenceIndexedTorusActionPaid : Bool
    incidenceIndexedTorusActionPaidIsTrue : incidenceIndexedTorusActionPaid ≡ true
    phaseInvariantConsumerDescentPaid : Bool
    phaseInvariantConsumerDescentPaidIsTrue : phaseInvariantConsumerDescentPaid ≡ true
    periodicObserverCore54FactorizationPaid : Bool
    periodicObserverCore54FactorizationPaidIsTrue :
      periodicObserverCore54FactorizationPaid ≡ true
    quotientSafeForArbitraryEngineeringObserver : Bool
    quotientSafeForArbitraryEngineeringObserverIsFalse :
      quotientSafeForArbitraryEngineeringObserver ≡ false
    hardNonAxisymmetricNumericalFibreReplayPaid : Bool
    hardNonAxisymmetricNumericalFibreReplayPaidIsTrue :
      hardNonAxisymmetricNumericalFibreReplayPaid ≡ true
    acceptedNonAxisymmetricPhysicalRealizationPaid : Bool
    acceptedNonAxisymmetricPhysicalRealizationPaidIsFalse :
      acceptedNonAxisymmetricPhysicalRealizationPaid ≡ false
    freeBoundaryEquilibriumPaid : Bool
    freeBoundaryEquilibriumPaidIsFalse : freeBoundaryEquilibriumPaid ≡ false
    fullOrbitBestReferencePaid : Bool
    fullOrbitBestReferencePaidIsFalse : fullOrbitBestReferencePaid ≡ false

canonicalPhase243MaxCutStatus : Phase243MaxCutStatus
canonicalPhase243MaxCutStatus =
  phase243-max-cut-status
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl

carrierWitness : Rook.coreCount + Rook.axisBoundaryCount ≡ Rook.rookPairCount
carrierWitness = Rook.rookSplitCloses

coreCarrierRoundTripWitness :
  (x : Rook.Core243) → Bridge.fromFiveTrits (Bridge.toFiveTrits x) ≡ x
coreCarrierRoundTripWitness = Bridge.coreFiveRoundTrip

phaseActionWitness :
  (x : Rook.Core243) →
  Bridge.toFiveTrits (Rook.advanceCore x)
  ≡ Action.advanceFiveTrits (Bridge.toFiveTrits x)
phaseActionWitness = Action.coreAdvanceIntertwines

quotientAdvanceWitness :
  (x : Rook.Core243) →
  Q54.quotientCore (Rook.advanceCore x) ≡ Q54.quotientCore x
quotientAdvanceWitness = Q54.quotientAdvanceInvariant

quotientRepresentativeWitness :
  (x : Q54.Core54) →
  Q54.quotientCore (Q54.representativeCore x) ≡ x
quotientRepresentativeWitness = Q54.quotientRepresentativeRoundTrip

torusAdvanceWitness :
  (x : Rook.Core243) →
  Torus.pullbackCoreByCanonicalAdvance x ≡ Rook.advanceCore x
torusAdvanceWitness = Torus.canonicalAdvancePullbackIntertwines

phaseInvariantDescentBoundary : Descent.Phase243ConsumerDescentBoundary
phaseInvariantDescentBoundary = Descent.canonicalPhase243ConsumerDescentBoundary

periodicConsumerQuotientBoundary : Periodic.PeriodicPhase243ConsumerBoundary
periodicConsumerQuotientBoundary =
  Periodic.canonicalPeriodicPhase243ConsumerBoundary

numericalReplayWitness : Fibre.Core54NumericalReplayReceipt
numericalReplayWitness = Fibre.canonicalCore54NumericalReplayReceipt

nextPhysicalFrontier : String
nextPhysicalFrontier =
  "Use Core54 only for observers with the explicit torus/reparameterization equivariance receipt.  Pareto-rank the surviving hard-nonaxis continuous fibres, run the current-potential coil inverse on that small set, replay the produced coil field, solve one same-object B_coil+B_plasma free-boundary finite-beta ABC equilibrium, then run zero-bounce/guiding-centre/FOW/energetic-particle consumers against the same best-known reference chart.  Reopen the 243 fibre wherever engineering geometry breaks the quotient symmetry."
