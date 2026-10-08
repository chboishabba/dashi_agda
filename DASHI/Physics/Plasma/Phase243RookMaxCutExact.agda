module DASHI.Physics.Plasma.Phase243RookMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.PhaseRook270Exact as Rook
import DASHI.Physics.Plasma.PhaseCore243FiveTritExact as Bridge
import DASHI.Physics.Plasma.Phase243ActionIntertwinerExact as Action
import DASHI.Physics.Plasma.Phase243PlasmaConsumerExact as Consumer

------------------------------------------------------------------------
-- CONSOLIDATED PHASE-243 MAX-CUT
--
-- Paid:
--   630 = 36 + 270 + 324 phase-resolved pair decomposition;
--   270 = 243 + 27 invariant rook split;
--   Core243 <-> FiveTrits total round-trip carrier recognition;
--   AxisBoundary27 <-> Ternary27Point total round-trip carrier recognition;
--   exact C3 advance / inversion action transport through both bijections.
--
-- Open physical frontier:
--   populate the 243 base with continuous geometry/current amplitudes while
--   preserving non-axisymmetry, then pay free-boundary coil+plasma equilibrium,
--   full orbit/FOW/EP consumers and same-chart best-known comparison.
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
    nonAxisymmetricPhysicalRealizationPaid : Bool
    nonAxisymmetricPhysicalRealizationPaidIsFalse :
      nonAxisymmetricPhysicalRealizationPaid ≡ false
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

nextPhysicalFrontier : String
nextPhysicalFrontier =
  "Enumerate/admissibility-rank Core243 as a finite base with continuous physical fibres; require a nonzero C3/non-axisymmetric realization, solve coil+plasma free-boundary ABC equilibrium on survivors, then run full guiding-centre/FOW/energetic-particle replay against the same best-known reference chart."
