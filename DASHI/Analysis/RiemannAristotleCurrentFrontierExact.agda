module DASHI.Analysis.RiemannAristotleCurrentFrontierExact where

------------------------------------------------------------------------
-- AUTHORITATIVE CURRENT FRONTIER FOR THE ARISTOTLE / RH LANE
--
-- Maintained bidirectionally: forward from machine-checked Lean owners and
-- backward from the unweakened RH contradiction.
--
-- §35--§38 are retained as audit/scalarization infrastructure. In particular,
-- the clustering inequality is a condition for positivity of a gap-split NO-GO
-- lower bound and is not a forward RH producer. The determinant G2d signed-sum
-- lane is likewise useful scalarization, but the authoritative pole-quotient
-- current cut explicitly does not identify the rank-two determinant taper with
-- the final universal pole-quotient taper.
--
-- The final high-ordinate consumer is the existing pole-quotient split
--
--   cluster = offOrdinate + Gamma
--   offOrdinate <= B_off
--   Gamma <= B_Gamma
--   B_off + B_Gamma < M_cluster.
--
-- Producer adequacy is now consumer-assigned:
--
--   B_off <= A_off
--   B_Gamma <= A_Gamma
--   A_off + A_Gamma < M_cluster.
--
-- The strict combined budget and final contradiction are compiler output. The
-- Off payment must be established at one common quarter-period crossing cutoff
-- J where signed near plus owned far fits A_off. Gamma has no J coordinate and
-- must fit A_Gamma on the same universal pole-quotient taper. The 8889 return
-- owns quantitative cluster-margin mathematics, leaving same-object attachment.
-- Source-order transport is downstream proof engineering and is compiled once
-- per source relation rather than by re-proving every transported inequality.
--
-- The live analytic-core owner now compiles the two theorem-bearing high-
-- ordinate cores, their representation attachments, and the already-owned
-- final same-object/order/cluster attachment directly to contradiction.
-- Therefore no further downstream high-ordinate theorem is on the research cut.
--
-- Low ordinates are independent.  The Platt--Trudgian published verified-zero
-- source is recovered in-repo, but no proof term/import has been promoted into
-- Agda.  Source recovery and Agda theorem attachment remain distinct.
--
-- No theorem here derives RH.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Analysis.RiemannG2PoleQuotientFinalCutReconciliationExact as FinalCut
import DASHI.Analysis.RiemannG2PoleQuotientProducerAllowanceTargetExact as AllowanceTarget
import DASHI.Analysis.RiemannG2PoleQuotientOffAllowanceDirectCompilerExact as OffDirect
import DASHI.Analysis.RiemannG2PoleQuotientGammaAllowanceDirectCompilerExact as GammaDirect
import DASHI.Analysis.RiemannG2FinalSplitComplementOrderTransportCompilerExact as OrderTransport
import DASHI.Analysis.RiemannG2FinalPoleQuotientAnalyticCoreExact as AnalyticCore
import DASHI.Analysis.DeBruijnNewman2026SourceWeldExact as DBN

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
    "The §35 clustering inequality and M2_delta are obstruction diagnostics, not forward RH payments. The determinant DirectSignedConsumerPayment remains a G2d scalarization theorem but does not automatically transport to the final universal pole-quotient taper. The authoritative high-ordinate mathematical cores are OffAnalyticCore and GammaAnalyticCore; once inhabited, their representation attachments plus the final same-object/order/cluster attachment compile directly to contradiction. Off must use one common quarter-period crossing cutoff J with B_near(J)+B_far(J)<=A_off; Gamma must satisfy B_Gamma(g_pole)<=A_Gamma on the same universal taper. Quantitative cluster-margin mathematics is owned in the 8889 checked-Lean return, while same-object/order attachment is downstream. Low-ordinate source coverage is recovered from Platt--Trudgian but its theorem/import is not promoted into Agda. RH remains open."

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

------------------------------------------------------------------------
-- Final-carrier precedence pins.
------------------------------------------------------------------------

determinantLaneIsNotFinalPoleQuotientCarrier :
  FinalCut.PoleQuotientFinalCutBoundary.determinantLaneIsFinalPoleQuotientCarrier
    FinalCut.canonicalPoleQuotientFinalCutBoundary ≡ false
determinantLaneIsNotFinalPoleQuotientCarrier = refl

determinantPaymentDoesNotAutoPayFinalOffSocket :
  FinalCut.PoleQuotientFinalCutBoundary.determinantDirectPaymentAutomaticallyPaysFinalOffSocket
    FinalCut.canonicalPoleQuotientFinalCutBoundary ≡ false
determinantPaymentDoesNotAutoPayFinalOffSocket = refl

universalPoleQuotientSignedOffIsForwardLeaf :
  FinalCut.PoleQuotientFinalCutBoundary.literalUniversalPoleQuotientSignedOffIsForwardLeaf
    FinalCut.canonicalPoleQuotientFinalCutBoundary ≡ true
universalPoleQuotientSignedOffIsForwardLeaf = refl

sameTaperGammaPrecisionIsForwardLeaf :
  FinalCut.PoleQuotientFinalCutBoundary.sameTaperGammaPrecisionIsForwardLeaf
    FinalCut.canonicalPoleQuotientFinalCutBoundary ≡ true
sameTaperGammaPrecisionIsForwardLeaf = refl

freshClusterMarginAnalysisNotRequired :
  FinalCut.PoleQuotientFinalCutBoundary.freshClusterMarginAnalysisRequired
    FinalCut.canonicalPoleQuotientFinalCutBoundary ≡ false
freshClusterMarginAnalysisNotRequired = refl

finalContradictionCompilerRebuildNotRequired :
  FinalCut.PoleQuotientFinalCutBoundary.finalContradictionCompilerNeedsRebuilding
    FinalCut.canonicalPoleQuotientFinalCutBoundary ≡ false
finalContradictionCompilerRebuildNotRequired = refl

------------------------------------------------------------------------
-- Terminal allowance / common-cutoff / order-transport pins.
------------------------------------------------------------------------

terminalOffPaymentType : Set₁
terminalOffPaymentType = AllowanceTarget.PoleQuotientOffAllowancePayment

terminalGammaPaymentType : Set₁
terminalGammaPaymentType = AllowanceTarget.PoleQuotientGammaAllowancePayment

terminalOffRequiresOneCommonCrossingCutoff :
  OffDirect.PoleQuotientOffAllowanceDirectCompilerBoundary.oneCommonCrossingCutoffRequired
    OffDirect.canonicalPoleQuotientOffAllowanceDirectCompilerBoundary ≡ true
terminalOffRequiresOneCommonCrossingCutoff = refl

terminalOffFarDecayAloneDoesNotSelectCutoff :
  OffDirect.PoleQuotientOffAllowanceDirectCompilerBoundary.farDecayAloneSelectsFinalCutoff
    OffDirect.canonicalPoleQuotientOffAllowanceDirectCompilerBoundary ≡ false
terminalOffFarDecayAloneDoesNotSelectCutoff = refl

terminalGammaHasNoCutoffCoordinate :
  GammaDirect.PoleQuotientGammaAllowanceDirectCompilerBoundary.gammaDependsOnQuarterPeriodCutoff
    GammaDirect.canonicalPoleQuotientGammaAllowanceDirectCompilerBoundary ≡ false
terminalGammaHasNoCutoffCoordinate = refl

finalOrderTransportCompilesContradiction :
  OrderTransport.FinalOrderTransportBoundary.orderTransportPackageCompilesContradiction
    OrderTransport.canonicalFinalOrderTransportBoundary ≡ true
finalOrderTransportCompilesContradiction = refl

------------------------------------------------------------------------
-- Exact current three-leaf global cut.
------------------------------------------------------------------------

highOrdinateAnalyticCoreCompilerOwned : Bool
highOrdinateAnalyticCoreCompilerOwned = true

highOrdinateAnalyticCoreCompilerOwnedIsTrue :
  highOrdinateAnalyticCoreCompilerOwned ≡ true
highOrdinateAnalyticCoreCompilerOwnedIsTrue = refl

highOrdinateCompletionTheorem : Set₁
highOrdinateCompletionTheorem =
  (cores : AnalyticCore.FinalPoleQuotientTwoAnalyticCores) ->
  (attachments : AnalyticCore.FinalPoleQuotientAnalyticCoreAttachments cores) ->
  AnalyticCore.FinalPoleQuotientAnalyticCompletion cores attachments ->
  ⊥

plattTrudgianLowOrdinateSourceRecovered : Bool
plattTrudgianLowOrdinateSourceRecovered = DBN.plattTrudgianSourceRecovered

plattTrudgianLowOrdinateSourceRecoveredIsTrue :
  plattTrudgianLowOrdinateSourceRecovered ≡ true
plattTrudgianLowOrdinateSourceRecoveredIsTrue = refl

plattTrudgianLowOrdinateTheoremImportedIntoAgda : Bool
plattTrudgianLowOrdinateTheoremImportedIntoAgda = false

plattTrudgianLowOrdinateTheoremImportedIntoAgdaIsFalse :
  plattTrudgianLowOrdinateTheoremImportedIntoAgda ≡ false
plattTrudgianLowOrdinateTheoremImportedIntoAgdaIsFalse = refl
