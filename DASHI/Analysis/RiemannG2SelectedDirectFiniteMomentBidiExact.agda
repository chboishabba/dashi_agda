module DASHI.Analysis.RiemannG2SelectedDirectFiniteMomentBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannG2FkOrbitConsumerAttachmentExact as Orbit
import DASHI.Analysis.RiemannG2SelectedPoleNearSingleProducerBidiExact as Selected
import DASHI.Analysis.RiemannAristotlePoleQuotientDirectFiniteNearAttackExact as Direct
import DASHI.Analysis.RiemannG2LowGapClusteringMomentReductionExact as Moment

------------------------------------------------------------------------
-- SELECTED WINDOW <-> DIRECT FINITE GAP/MOMENT BIDI WELD
--
-- Existing owners already separate two useful views of the same intended
-- mathematical object:
--
--   * ActualSelectedPoleNearProducer: exact selected Weil/formula/window object;
--   * DirectFinitePoleNearProducer: explicit finite zero-index carrier with
--       multiplicity, horizontal displacement, targetRelativeGap and signed
--       cosine evaluation.
--
-- This module does NOT invent another zero family. It records the exact bridge
-- required to assert that a DirectFinitePoleNearProducer realizes the SAME
-- selected target/window. The local ordinate-moment ledger is then attached to
-- that direct producer, so the same delta data can feed both:
--
--   (a) low-gap clustering, through the moment compiler; and
--   (b) the direct signed finite-near evaluation already carried by `direct`.
------------------------------------------------------------------------

record SelectedDirectFiniteWeld
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (orbit : Orbit.SourceFkOrbit)
    (selected : Selected.ActualSelectedPoleNearProducer space formula orbit)
    (direct : Direct.DirectFinitePoleNearProducer) : Set₁ where
  field
    sameSelectedTarget : Set
    sameSelectedCutoff : Set
    sameNearZeroIndexFamily : Set
    sameMultiplicityFunction : Set
    sameTargetRelativeGapFunction : Set
    samePoleTaper : Set
    sameFiniteSignedNearValue : Set
    sameExplicitFormulaObject : Set
    weldReference : String

open SelectedDirectFiniteWeld public

record SelectedDirectFiniteMomentProducer
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (orbit : Orbit.SourceFkOrbit)
    (selected : Selected.ActualSelectedPoleNearProducer space formula orbit)
    (direct : Direct.DirectFinitePoleNearProducer)
    (weld : SelectedDirectFiniteWeld space formula orbit selected direct) : Set₁ where
  field
    normalizedOrdinateMoment : Moment.NormalizedLocalSecondMomentLedger

    momentBuiltFromDirectTargetRelativeGap : Set
    momentUsesDirectNearIndex : Set
    momentUsesDirectMultiplicity : Set
    radiusIsSelectedGapSplitD : Set
    everyHighGapCellPaysUnitNormalizedMoment : Set

    momentReference : String

open SelectedDirectFiniteMomentProducer public

selectedDirectMomentGivesTwoToOneRatio :
  ∀ {space formula orbit selected direct weld} →
  (producer :
    SelectedDirectFiniteMomentProducer
      space formula orbit selected direct weld) →
  Moment.HighMassStrictlyBelowTwiceLow
    (SelectedDirectFiniteMomentProducer.normalizedOrdinateMoment producer)
selectedDirectMomentGivesTwoToOneRatio producer =
  Moment.localSecondMomentForcesTwoToOneMassRatio
    (SelectedDirectFiniteMomentProducer.normalizedOrdinateMoment producer)

------------------------------------------------------------------------
-- Fan-out: one admitted direct producer already has the signed finite-near
-- evaluation receipt, while the attached moment supplies the clustering ratio.
------------------------------------------------------------------------

directEvaluationReceiptStillAvailable :
  ∀ {space formula orbit selected direct weld} →
  SelectedDirectFiniteMomentProducer
    space formula orbit selected direct weld →
  Direct.DirectFinitePoleNearProducer.Within direct
    (Direct.DirectFinitePoleNearProducer.finiteSignedNearValue direct)
    (Direct.DirectFinitePoleNearProducer.approximant direct)
    (Direct.DirectFinitePoleNearProducer.error direct)
directEvaluationReceiptStillAvailable {direct = direct} producer =
  Direct.DirectFinitePoleNearProducer.evaluationReceipt direct

------------------------------------------------------------------------
-- Search compression / authority boundary.
------------------------------------------------------------------------

data SharedZeroSidePayment : Set where
  recoverSecondSelectedWindow
  recoverSecondDirectZeroFamily
  weldExistingDirectProducerToSelectedWindow
  proveOrdinateMomentOnWeldedDirectProducer
  evaluateSignedFiniteNearOnWeldedDirectProducer
  transportMomentRatioToExactClusteringCoefficient
  : SharedZeroSidePayment

data PaymentState : Set where
  pruned live downstream : PaymentState

paymentState : SharedZeroSidePayment → PaymentState
paymentState recoverSecondSelectedWindow = pruned
paymentState recoverSecondDirectZeroFamily = pruned
paymentState weldExistingDirectProducerToSelectedWindow = live
paymentState proveOrdinateMomentOnWeldedDirectProducer = live
paymentState evaluateSignedFiniteNearOnWeldedDirectProducer = live
paymentState transportMomentRatioToExactClusteringCoefficient = downstream

secondSelectedWindowPruned :
  paymentState recoverSecondSelectedWindow ≡ pruned
secondSelectedWindowPruned = refl

secondDirectZeroFamilyPruned :
  paymentState recoverSecondDirectZeroFamily ≡ pruned
secondDirectZeroFamilyPruned = refl

record SelectedDirectFiniteMomentBoundary : Set where
  constructor selected-direct-finite-moment-boundary
  field
    selectedAndDirectViewsMustBeWelded : Bool
    selectedAndDirectViewsMustBeWeldedIsTrue :
      selectedAndDirectViewsMustBeWelded ≡ true

    separateZeroFamilyForMomentRequired : Bool
    separateZeroFamilyForMomentRequiredIsFalse :
      separateZeroFamilyForMomentRequired ≡ false

    oneDirectGapCarrierCanFeedClusteringAndFiniteEvaluation : Bool
    oneDirectGapCarrierCanFeedClusteringAndFiniteEvaluationIsTrue :
      oneDirectGapCarrierCanFeedClusteringAndFiniteEvaluation ≡ true

    selectedDirectWeldInhabitedHere : Bool
    selectedDirectWeldInhabitedHereIsFalse :
      selectedDirectWeldInhabitedHere ≡ false

    selectedDirectMomentProducerInhabitedHere : Bool
    selectedDirectMomentProducerInhabitedHereIsFalse :
      selectedDirectMomentProducerInhabitedHere ≡ false

    directFiniteEvaluationClosedHere : Bool
    directFiniteEvaluationClosedHereIsFalse :
      directFiniteEvaluationClosedHere ≡ false

    exactClusteringClosedHere : Bool
    exactClusteringClosedHereIsFalse : exactClusteringClosedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

open SelectedDirectFiniteMomentBoundary public

canonicalSelectedDirectFiniteMomentBoundary : SelectedDirectFiniteMomentBoundary
canonicalSelectedDirectFiniteMomentBoundary =
  selected-direct-finite-moment-boundary
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "The highest-fanout zero-side object is not a new phase ontology. Weld an existing DirectFinitePoleNearProducer to the existing ActualSelectedPoleNearProducer, then derive the normalized ordinate-gap moment from that direct targetRelativeGap/multiplicity/nearIndex carrier. The same direct producer already carries the signed finite-near evaluation receipt, so one same-object zero carrier can feed both clustering and H_off evaluation. The weld, actual moment estimate, actual finite evaluation, coefficient transport and RH remain unproved here."
