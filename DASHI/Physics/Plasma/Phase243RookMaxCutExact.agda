module DASHI.Physics.Plasma.Phase243RookMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.PhaseRook270Exact as Rook
import DASHI.Physics.Plasma.PhaseCore243FiveTritExact as Bridge
import DASHI.Physics.Plasma.Phase243ActionIntertwinerExact as Action
import DASHI.Physics.Plasma.Phase243OrbitQuotientExact as Q54
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
--   explicit equivariance gate before a physical consumer may use that quotient;
--   low-resolution hard-nonaxis 54-representative physical replay.
--
-- Open physical frontier:
--   replace the toy surface-field fibre by same-object coil+plasma free-boundary
--   equilibrium, then pay full orbit/FOW/EP consumers and same-chart best-known
--   comparison.  The numerical Core54 winner is reconnaissance, not acceptance.
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
    quotientConsumerEquivarianceGatePaid : Bool
    quotientConsumerEquivarianceGatePaidIsTrue : quotientConsumerEquivarianceGatePaid ≡ true
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

numericalReplayWitness : Fibre.Core54NumericalReplayReceipt
numericalReplayWitness = Fibre.canonicalCore54NumericalReplayReceipt

nextPhysicalFrontier : String
nextPhysicalFrontier =
  "Search only the 54 phase-action representatives for consumers with an explicit equivariance receipt; lift surviving hard-nonaxis fibres into the current-potential coil inverse, solve same-object coil+plasma free-boundary ABC equilibrium, then run guiding-centre/FOW/energetic-particle replay against the same best-known reference chart."
