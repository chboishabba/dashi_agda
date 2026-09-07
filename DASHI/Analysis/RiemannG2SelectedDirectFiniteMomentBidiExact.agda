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
--   * DirectFinitePoleNearProducer: literal zero/gap + signed evaluation;
--   * LiteralTargetCenteredScalarProblem: final G2 q/zero/target consumer.
--
-- Every same-object proposition below is proof-bearing. Merely supplying a Set
-- no longer counts as a weld receipt.
------------------------------------------------------------------------

record SelectedDirectFiniteWeld
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (orbit : Orbit.SourceFkOrbit)
    (selected : Selected.ActualSelectedPoleNearProducer space formula orbit)
    (direct : Direct.DirectFinitePoleNearProducer) : Set₁ where
  field
    sameSelectedTarget : Set
    sameSelectedTargetReceipt : sameSelectedTarget

    sameSelectedCutoff : Set
    sameSelectedCutoffReceipt : sameSelectedCutoff

    sameNearZeroIndexFamily : Set
    sameNearZeroIndexFamilyReceipt : sameNearZeroIndexFamily

    sameMultiplicityFunction : Set
    sameMultiplicityFunctionReceipt : sameMultiplicityFunction

    sameTargetRelativeGapFunction : Set
    sameTargetRelativeGapFunctionReceipt : sameTargetRelativeGapFunction

    samePoleTaper : Set
    samePoleTaperReceipt : samePoleTaper

    sameFiniteSignedNearValue : Set
    sameFiniteSignedNearValueReceipt : sameFiniteSignedNearValue

    sameExplicitFormulaObject : Set
    sameExplicitFormulaObjectReceipt : sameExplicitFormulaObject

    selectedWindowIsDirectLiteralProblem : Set
    selectedWindowIsDirectLiteralProblemReceipt :
      selectedWindowIsDirectLiteralProblem

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

    -- The Nat ledger is not a second mathematical moment. It must realize the
    -- exact literal Scalar-valued moment under an explicit normalization/order.
    normalizedLedgerRealizesLiteralTargetGapSecondMoment : Set
    normalizedLedgerRealizesLiteralTargetGapSecondMomentReceipt :
      normalizedLedgerRealizesLiteralTargetGapSecondMoment

    normalizationPreservesLiteralNearFamily : Set
    normalizationPreservesLiteralNearFamilyReceipt :
      normalizationPreservesLiteralNearFamily

    normalizationPreservesLiteralMultiplicity : Set
    normalizationPreservesLiteralMultiplicityReceipt :
      normalizationPreservesLiteralMultiplicity

    radiusIsSelectedGapSplitD : Set
    radiusIsSelectedGapSplitDReceipt : radiusIsSelectedGapSplitD

    everyHighGapCellPaysUnitNormalizedMoment : Set
    everyHighGapCellPaysUnitNormalizedMomentReceipt :
      everyHighGapCellPaysUnitNormalizedMoment

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
-- evaluation receipt, while the downstream moment supplies clustering ratio.
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
  recoverSecondSelectedWindow : SharedZeroSidePayment
  recoverSecondDirectZeroFamily : SharedZeroSidePayment
  recoverDirectFinitePoleNearProducer : SharedZeroSidePayment
  weldExistingDirectProducerToSelectedWindow : SharedZeroSidePayment
  constructSecondMomentDefinition : SharedZeroSidePayment
  proveLiteralOrdinateMomentBoundAfterWeld : SharedZeroSidePayment
  reEvaluateSignedFiniteNearAfterDirectProducer : SharedZeroSidePayment
  attachDirectEvaluationToSelectedConsumer : SharedZeroSidePayment
  transportMomentRatioToExactClusteringCoefficient : SharedZeroSidePayment


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

    selectedDirectWeldClaimsAreProofBearing : Bool
    selectedDirectWeldClaimsAreProofBearingIsTrue :
      selectedDirectWeldClaimsAreProofBearing ≡ true

    momentNormalizationClaimsAreProofBearing : Bool
    momentNormalizationClaimsAreProofBearingIsTrue :
      momentNormalizationClaimsAreProofBearing ≡ true

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
    true refl
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
    "The literal delta moment is not a free-floating search object. DirectFinitePoleNearProducer names the canonical LiteralTargetCenteredScalarProblem, which owns M2_delta = finiteNearSum(m_sigma*(ordinate-target)^2). Recover the actual direct quantitative receipt first; then provide proof-bearing selected/direct same-object weld receipts. Any normalized clustering ledger must itself carry proof-bearing realization receipts back to that literal M2_delta. Do not re-evaluate a second finite sum or define a second moment. Exact clustering and RH remain open."
