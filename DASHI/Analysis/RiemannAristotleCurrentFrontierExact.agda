module DASHI.Analysis.RiemannAristotleCurrentFrontierExact where

------------------------------------------------------------------------
-- AUTHORITATIVE CURRENT FRONTIER FOR THE ARISTOTLE / RH LANE
--
-- Maintained bidirectionally: forward from machine-checked Lean owners and
-- backward from the unweakened RH contradiction.
--
-- §37 reconciles density cutoff with quarter-period crossing and §38 instantiates
-- zeta's upper local count. These close two audit coordinates.
--
-- IMPORTANT CORRECTION AFTER SOURCE RE-READ
--
-- §35 proves
--
--   positive gap-split lower bound
--      -> (4/pi^2) * highGapMass < lowGapMass.
--
-- The positive lower bound is used by the checked no-go theorems to show the
-- desired small signed-scalar hypothesis is unsatisfiable when the floor reaches
-- the consumer threshold. Hence the clustering inequality is an OBSTRUCTION
-- DIAGNOSTIC, not the first forward RH theorem.
--
-- The forward G2d/current-cut theorem remains the literal signed target-centred
-- determinant response. BIDI compression now states it exactly as
--
--   DirectSignedConsumerPayment P
--     = AcceptableForG2Consumer P (totalSignedResponse P)
--
-- on the canonical LiteralTargetCenteredScalarProblem. A successful
-- DirectFinitePoleNearProducer must carry this payment. Canonical Scalar,
-- ZeroIndex, target, nearOff, multiplicity, off-real displacement, delta and
-- totalSignedResponse compile from P; PoleNearPhaseStatistic and the generic
-- evaluation surface compile from the direct producer.
--
-- Selected-window identity and selected-scalar budget transport are downstream
-- after the direct producer. The literal M2_delta is still a useful diagnostic
-- observable for the gap-split obstruction, but is not a forward RH payment.
-- Gamma precision remains an independent live branch. Projective balance,
-- low-ordinate/global coverage and RH remain separate.
--
-- No theorem here derives RH.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record AristotleCurrentFrontier : Set where
  constructor aristotle-current-frontier
  field
    universalEvenConeConstructionClosedInLean : Bool
    universalEvenConeConstructionClosedInLeanIsTrue :
      universalEvenConeConstructionClosedInLean ≡ true

    twoRadiusOffLineDiscriminatorClosedInLean : Bool
    twoRadiusOffLineDiscriminatorClosedInLeanIsTrue :
      twoRadiusOffLineDiscriminatorClosedInLean ≡ true

    highOrdinatePrimeProjectiveDebtZeroInLean : Bool
    highOrdinatePrimeProjectiveDebtZeroInLeanIsTrue :
      highOrdinatePrimeProjectiveDebtZeroInLean ≡ true

    deterministicProjectiveSchurKernelCheckedInLean : Bool
    deterministicProjectiveSchurKernelCheckedInLeanIsTrue :
      deterministicProjectiveSchurKernelCheckedInLean ≡ true

    explicitFarShellCutoffBoundClosedInLean : Bool
    explicitFarShellCutoffBoundClosedInLeanIsTrue :
      explicitFarShellCutoffBoundClosedInLean ≡ true

    explicitFarShellTendsToZeroClosedInLean : Bool
    explicitFarShellTendsToZeroClosedInLeanIsTrue :
      explicitFarShellTendsToZeroClosedInLean ≡ true

    finiteSignedNearCarrierClosedInLean : Bool
    finiteSignedNearCarrierClosedInLeanIsTrue :
      finiteSignedNearCarrierClosedInLean ≡ true

    literalDoffCutoffCarrierClosedInLean : Bool
    literalDoffCutoffCarrierClosedInLeanIsTrue :
      literalDoffCutoffCarrierClosedInLean ≡ true

    latestLeanBridgeBuildKernelChecked : Bool
    latestLeanBridgeBuildKernelCheckedIsTrue :
      latestLeanBridgeBuildKernelChecked ≡ true

    quarterPeriodDensityReconciliationClosedInLean : Bool
    quarterPeriodDensityReconciliationClosedInLeanIsTrue :
      quarterPeriodDensityReconciliationClosedInLean ≡ true

    zetaUnitLocalCountClosedInLean : Bool
    zetaUnitLocalCountClosedInLeanIsTrue :
      zetaUnitLocalCountClosedInLean ≡ true

    zetaShortWindowUpperCountClosedInLean : Bool
    zetaShortWindowUpperCountClosedInLeanIsTrue :
      zetaShortWindowUpperCountClosedInLean ≡ true

    densityCutRefutesInverseWidthRoute : Bool
    densityCutRefutesInverseWidthRouteIsFalse :
      densityCutRefutesInverseWidthRoute ≡ false

    zetaLongWindowLowerDensityClosed : Bool
    zetaLongWindowLowerDensityClosedIsFalse :
      zetaLongWindowLowerDensityClosed ≡ false

    actualZetaClusteringClosed : Bool
    actualZetaClusteringClosedIsFalse : actualZetaClusteringClosed ≡ false

    targetLocalSecondMomentCompilerClosedInAgda : Bool
    targetLocalSecondMomentCompilerClosedInAgdaIsTrue :
      targetLocalSecondMomentCompilerClosedInAgda ≡ true

    targetLocalSecondMomentProducerClosed : Bool
    targetLocalSecondMomentProducerClosedIsFalse :
      targetLocalSecondMomentProducerClosed ≡ false

    targetLocalMomentUsesExistingSelectedWindow : Bool
    targetLocalMomentUsesExistingSelectedWindowIsTrue :
      targetLocalMomentUsesExistingSelectedWindow ≡ true

    concretePhaseStatisticCompilerClosedInAgda : Bool
    concretePhaseStatisticCompilerClosedInAgdaIsTrue :
      concretePhaseStatisticCompilerClosedInAgda ≡ true

    selectedDirectZeroCarrierWeldClosed : Bool
    selectedDirectZeroCarrierWeldClosedIsFalse :
      selectedDirectZeroCarrierWeldClosed ≡ false

    oneDirectGapCarrierFeedsClusteringAndFiniteNear : Bool
    oneDirectGapCarrierFeedsClusteringAndFiniteNearIsTrue :
      oneDirectGapCarrierFeedsClusteringAndFiniteNear ≡ true

    transverseMomentDirectlyControlsOrdinateClustering : Bool
    transverseMomentDirectlyControlsOrdinateClusteringIsFalse :
      transverseMomentDirectlyControlsOrdinateClustering ≡ false

    alpogeFurmanGlobalSimpleProportionDirectlyClosesClustering : Bool
    alpogeFurmanGlobalSimpleProportionDirectlyClosesClusteringIsFalse :
      alpogeFurmanGlobalSimpleProportionDirectlyClosesClustering ≡ false

    nearFarShellCompositionCompilerClosedInAgda : Bool
    nearFarShellCompositionCompilerClosedInAgdaIsTrue :
      nearFarShellCompositionCompilerClosedInAgda ≡ true

    nearFarAllowanceCompilerClosedInAgda : Bool
    nearFarAllowanceCompilerClosedInAgdaIsTrue :
      nearFarAllowanceCompilerClosedInAgda ≡ true

    finiteNearCoreSchurPerturbationCompilerClosedInAgda : Bool
    finiteNearCoreSchurPerturbationCompilerClosedInAgdaIsTrue :
      finiteNearCoreSchurPerturbationCompilerClosedInAgda ≡ true

    explicitLeanTailFormulaTransportedAsAgdaProof : Bool
    explicitLeanTailFormulaTransportedAsAgdaProofIsFalse :
      explicitLeanTailFormulaTransportedAsAgdaProof ≡ false

    finiteSignedNearSchurCancellationClosed : Bool
    finiteSignedNearSchurCancellationClosedIsFalse :
      finiteSignedNearSchurCancellationClosed ≡ false

    jointFiniteNearFarMarginClosed : Bool
    jointFiniteNearFarMarginClosedIsFalse :
      jointFiniteNearFarMarginClosed ≡ false

    deterministicNuisanceThreeTaperConstructionClosed : Bool
    deterministicNuisanceThreeTaperConstructionClosedIsFalse :
      deterministicNuisanceThreeTaperConstructionClosed ≡ false

    lowOrdinateComplementCertified : Bool
    lowOrdinateComplementCertifiedIsFalse :
      lowOrdinateComplementCertified ≡ false

    finalRHImplicationClosed : Bool
    finalRHImplicationClosedIsFalse : finalRHImplicationClosed ≡ false

    boundedReading : String

open AristotleCurrentFrontier public

canonicalAristotleCurrentFrontier : AristotleCurrentFrontier
canonicalAristotleCurrentFrontier =
  aristotle-current-frontier
    true refl
    true refl
    true refl
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
    false refl
    false refl
    true refl
    false refl
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "The checked Lean tranche closes quarter-period/density compatibility and zeta upper local counting. The §35 inequality (4/pi^2)*highGapMass < lowGapMass is retained as a condition for positivity of the gap-split NO-GO lower bound, not as a forward RH producer. The forward zero-side leaf is the literal target-centred signed determinant estimate, now typed as DirectSignedConsumerPayment = AcceptableForG2Consumer(totalSignedResponse) on the canonical LiteralTargetCenteredScalarProblem and required by DirectFinitePoleNearProducer. Canonical zero/gap fields, the phase-statistic view and generic evaluation surface are compiler output; selected-window/budget transport is downstream. M2_delta remains a same-carrier obstruction diagnostic, not an RH payment. Gamma precision, projective-balance breaking, low-ordinate coverage and final RH remain open. RH is not derived."

------------------------------------------------------------------------
-- Corrected high-level scheduler interpretation, kept outside the compatibility
-- record so existing field projections remain stable.
------------------------------------------------------------------------

actualZetaClusteringIsForwardRHProducer : Bool
actualZetaClusteringIsForwardRHProducer = false

actualZetaClusteringIsForwardRHProducerIsFalse :
  actualZetaClusteringIsForwardRHProducer ≡ false
actualZetaClusteringIsForwardRHProducerIsFalse = refl

actualZetaClusteringIsGapSplitObstructionDiagnostic : Bool
actualZetaClusteringIsGapSplitObstructionDiagnostic = true

actualZetaClusteringIsGapSplitObstructionDiagnosticIsTrue :
  actualZetaClusteringIsGapSplitObstructionDiagnostic ≡ true
actualZetaClusteringIsGapSplitObstructionDiagnosticIsTrue = refl

targetLocalSecondMomentIsForwardRHProducer : Bool
targetLocalSecondMomentIsForwardRHProducer = false

targetLocalSecondMomentIsForwardRHProducerIsFalse :
  targetLocalSecondMomentIsForwardRHProducer ≡ false
targetLocalSecondMomentIsForwardRHProducerIsFalse = refl

directSignedConsumerPaymentCompilerClosedInAgda : Bool
directSignedConsumerPaymentCompilerClosedInAgda = true

directSignedConsumerPaymentCompilerClosedInAgdaIsTrue :
  directSignedConsumerPaymentCompilerClosedInAgda ≡ true
directSignedConsumerPaymentCompilerClosedInAgdaIsTrue = refl

literalDirectFiniteProducerClosed : Bool
literalDirectFiniteProducerClosed = false

literalDirectFiniteProducerClosedIsFalse :
  literalDirectFiniteProducerClosed ≡ false
literalDirectFiniteProducerClosedIsFalse = refl

genericWithinReceiptAloneClosesLiteralG2 : Bool
genericWithinReceiptAloneClosesLiteralG2 = false

genericWithinReceiptAloneClosesLiteralG2IsFalse :
  genericWithinReceiptAloneClosesLiteralG2 ≡ false
genericWithinReceiptAloneClosesLiteralG2IsFalse = refl
