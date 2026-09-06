module DASHI.Analysis.RiemannG2SelectedDirectFiniteMomentBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannG2FkOrbitConsumerAttachmentExact as Orbit
import DASHI.Analysis.RiemannG2SelectedPoleNearSingleProducerBidiExact as Selected
import DASHI.Analysis.RiemannAristotlePoleQuotientDirectFiniteNearAttackExact as Direct
import DASHI.Analysis.RiemannG2TargetCenteredScalarCancellationAssemblyExact as Literal
import DASHI.Analysis.RiemannG2LowGapClusteringMomentReductionExact as Moment

------------------------------------------------------------------------
-- SELECTED WINDOW <-> DIRECT FINITE GAP/MOMENT BIDI WELD
--
-- Existing owners expose three views of one intended mathematical object:
--
--   * ActualSelectedPoleNearProducer: selected Weil/formula/window object;
--   * DirectFinitePoleNearProducer: explicit zero/gap + signed evaluation;
--   * LiteralTargetCenteredScalarProblem: final G2 q/zero/target consumer.
--
-- The direct producer has now been strengthened in place: it names the literal
-- scalar problem it realizes. Therefore this module does not introduce another
-- moment definition. The only canonical unnormalised target-gap moment is
--
--   Literal.targetRelativeGapSecondMoment (Direct.literalProblem direct).
--
-- The normalized Nat ledger below must be an explicit normalization/ordering
-- realization of that literal scalar value. This keeps the discrete clustering
-- compiler honest without pretending an arbitrary Scalar is Nat.
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
    selectedWindowIsDirectLiteralProblem : Set
    weldReference : String

open SelectedDirectFiniteWeld public

literalTargetGapSecondMomentOfDirect :
  (direct : Direct.DirectFinitePoleNearProducer) →
  Literal.Scalar (Direct.literalProblem direct)
literalTargetGapSecondMomentOfDirect direct =
  Literal.targetRelativeGapSecondMoment (Direct.literalProblem direct)

record SelectedDirectFiniteMomentProducer
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (orbit : Orbit.SourceFkOrbit)
    (selected : Selected.ActualSelectedPoleNearProducer space formula orbit)
    (direct : Direct.DirectFinitePoleNearProducer)
    (weld : SelectedDirectFiniteWeld space formula orbit selected direct) : Set₁ where
  field
    normalizedOrdinateMoment : Moment.NormalizedLocalSecondMomentLedger

    -- The Nat ledger is not a second mathematical moment. It must be proved to
    -- represent the exact literal Scalar-valued moment above under the selected
    -- normalization/order structure.
    normalizedLedgerRealizesLiteralTargetGapSecondMoment : Set
    normalizationPreservesLiteralNearFamily : Set
    normalizationPreservesLiteralMultiplicity : Set
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
-- evaluation receipt, while the downstream moment supplies the clustering ratio.
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
  recoverDirectFinitePoleNearProducer
  weldExistingDirectProducerToSelectedWindow
  constructSecondMomentDefinition
  proveLiteralOrdinateMomentBoundAfterWeld
  reEvaluateSignedFiniteNearAfterDirectProducer
  attachDirectEvaluationToSelectedConsumer
  transportMomentRatioToExactClusteringCoefficient
  : SharedZeroSidePayment

data PaymentState : Set where
  pruned live downstream : PaymentState

paymentState : SharedZeroSidePayment → PaymentState
paymentState recoverSecondSelectedWindow = pruned
paymentState recoverSecondDirectZeroFamily = pruned
paymentState recoverDirectFinitePoleNearProducer = live
paymentState weldExistingDirectProducerToSelectedWindow = downstream
paymentState constructSecondMomentDefinition = pruned
paymentState proveLiteralOrdinateMomentBoundAfterWeld = downstream
paymentState reEvaluateSignedFiniteNearAfterDirectProducer = pruned
paymentState attachDirectEvaluationToSelectedConsumer = downstream
paymentState transportMomentRatioToExactClusteringCoefficient = downstream

secondSelectedWindowPruned :
  paymentState recoverSecondSelectedWindow ≡ pruned
secondSelectedWindowPruned = refl

secondDirectZeroFamilyPruned :
  paymentState recoverSecondDirectZeroFamily ≡ pruned
secondDirectZeroFamilyPruned = refl

secondMomentDefinitionPruned :
  paymentState constructSecondMomentDefinition ≡ pruned
secondMomentDefinitionPruned = refl

secondFiniteEvaluationPruned :
  paymentState reEvaluateSignedFiniteNearAfterDirectProducer ≡ pruned
secondFiniteEvaluationPruned = refl

record SelectedDirectFiniteMomentBoundary : Set where
  constructor selected-direct-finite-moment-boundary
  field
    selectedAndDirectViewsMustBeWelded : Bool
    selectedAndDirectViewsMustBeWeldedIsTrue :
      selectedAndDirectViewsMustBeWelded ≡ true

    separateZeroFamilyForMomentRequired : Bool
    separateZeroFamilyForMomentRequiredIsFalse :
      separateZeroFamilyForMomentRequired ≡ false

    literalTargetGapMomentAlreadyDefinedOnDirectProblem : Bool
    literalTargetGapMomentAlreadyDefinedOnDirectProblemIsTrue :
      literalTargetGapMomentAlreadyDefinedOnDirectProblem ≡ true

    secondMomentDefinitionRequired : Bool
    secondMomentDefinitionRequiredIsFalse : secondMomentDefinitionRequired ≡ false

    oneDirectGapCarrierCanFeedClusteringAndFiniteEvaluation : Bool
    oneDirectGapCarrierCanFeedClusteringAndFiniteEvaluationIsTrue :
      oneDirectGapCarrierCanFeedClusteringAndFiniteEvaluation ≡ true

    selectedDirectWeldInhabitedHere : Bool
    selectedDirectWeldInhabitedHereIsFalse : selectedDirectWeldInhabitedHere ≡ false

    selectedDirectMomentProducerInhabitedHere : Bool
    selectedDirectMomentProducerInhabitedHereIsFalse :
      selectedDirectMomentProducerInhabitedHere ≡ false

    secondSignedEvaluationRequiredAfterDirectProducer : Bool
    secondSignedEvaluationRequiredAfterDirectProducerIsFalse :
      secondSignedEvaluationRequiredAfterDirectProducer ≡ false

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
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "The literal delta moment is no longer a free-floating search object: DirectFinitePoleNearProducer names a LiteralTargetCenteredScalarProblem, and that owner defines M2_delta = finiteNearSum(m_sigma*(ordinate-target)^2). Recover the actual direct producer first. Its signed approximant/error receipt is already part of that object, so do not re-evaluate a second finite sum. After the direct producer and existing selected producer are available, weld them; then prove the quantitative bound on the SAME literal M2_delta and attach the existing direct evaluation to the selected consumer. The discrete two-to-one compiler is downstream, and RH remains open."
