module DASHI.Analysis.RiemannG2HighestAlphaAfter8894Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2GapSplitClusteringLeanReturn8894Exact as Gap
import DASHI.Analysis.RiemannG2Zeta23FkActionRecoveryExact as Fk
import DASHI.Analysis.RiemannG2Zeta23FkCheckedSourceReturnExact as FkChecked
import DASHI.Analysis.RiemannG2FkOrbitConsumerAttachmentExact as Orbit
import DASHI.Analysis.RiemannG2FkOrbitExplicitFormulaWeldExact as Weld
import DASHI.Analysis.RiemannG2FkSelectedTestSameObjectBidiExact as Same
import DASHI.Analysis.RiemannG2SelectedPoleNearSingleProducerBidiExact as Single
import DASHI.Analysis.RiemannG2SelectedPoleNearFiniteEvaluationSameObjectExact as NearEval
import DASHI.Analysis.RiemannG2PoleQuotientProducerReconciliation8889Exact as PQ

------------------------------------------------------------------------
-- HIGHEST-ALPHA SCHEDULER AFTER 8894 + PR CROSS-POLLINATION
--
-- The selected target-window representation work is one dependent producer.
-- The checked 8883 cutoff return separately owns the finite near carrier, far
-- shell, arbitrary-accuracy cutoff and literal D_off cutoff transport.  Hence
-- the live near-side analysis is now an actual phase-preserving FiniteNearProducer
-- welded to the exact finitePoleNearSigned coordinate of that selected window.
------------------------------------------------------------------------

data RH8894Leaf : Set where
  searchForModulationOperation
  rebuildCharacterMultiplication
  identifyWholeSourceFunctionSpaceWithWeilTest
  identifyWholeSourceFunctionSpaceWithMellinTest
  separatelyRecoverSelectedFkOrbitAttachment
  separatelyRecoverSelectedNearFarWeld
  separatelyRecoverSelectedSameTestWeld
  recoverActualSelectedPoleNearProducer

  rebuildFiniteNearCarrier
  reproveFarShellDecay
  reproveArbitraryAccuracyCutoff
  recoverPhasePreservingFiniteNearProducer
  weldFiniteNearEvaluationToSelectedWindow
  extractSelectedNearBudget

  sharpenQuadraticDecayGapSplit
  retuneTaperForGapSplit
  deriveClusteringFromCoarseCounting
  compareAdaptiveJLambdaConstants

  searchForAnyGammaBound
  localizeGammaPrecisionLoss
  repairGammaToSharpWindow
  attachOwnedClusterMargin
  combineFinalIndependentBudgets
  : RH8894Leaf

data LeafState : Set where
  pruned owned live conditional downstream : LeafState

leafState : RH8894Leaf -> LeafState
leafState searchForModulationOperation = owned
leafState rebuildCharacterMultiplication = pruned
leafState identifyWholeSourceFunctionSpaceWithWeilTest = pruned
leafState identifyWholeSourceFunctionSpaceWithMellinTest = pruned
leafState separatelyRecoverSelectedFkOrbitAttachment = pruned
leafState separatelyRecoverSelectedNearFarWeld = pruned
leafState separatelyRecoverSelectedSameTestWeld = pruned
leafState recoverActualSelectedPoleNearProducer = live

leafState rebuildFiniteNearCarrier = pruned
leafState reproveFarShellDecay = pruned
leafState reproveArbitraryAccuracyCutoff = pruned
leafState recoverPhasePreservingFiniteNearProducer = live
leafState weldFiniteNearEvaluationToSelectedWindow = live
leafState extractSelectedNearBudget = downstream

leafState sharpenQuadraticDecayGapSplit = pruned
leafState retuneTaperForGapSplit = pruned
leafState deriveClusteringFromCoarseCounting = pruned
leafState compareAdaptiveJLambdaConstants = live

leafState searchForAnyGammaBound = pruned
leafState localizeGammaPrecisionLoss = live
leafState repairGammaToSharpWindow = live
leafState attachOwnedClusterMargin = live
leafState combineFinalIndependentBudgets = conditional

------------------------------------------------------------------------
-- Scheduler agreement with existing pruning/source owners.
------------------------------------------------------------------------

modulationOperationSearchNoLongerLive :
  Fk.HARelevant Fk.searchForAnyModulationOperation -> ⊥
modulationOperationSearchNoLongerLive = Fk.modulationSearchPruned

sourceShiftReproofNoLongerLive :
  FkChecked.FkSourceRelevant FkChecked.reproveSourcePaperFTShift -> ⊥
sourceShiftReproofNoLongerLive = FkChecked.sourceShiftReproofPruned

wholeWeilCarrierEqualityNoLongerLive :
  Orbit.PaymentRelevant Orbit.identifyWholeSourceFunctionSpaceWithWeilTest -> ⊥
wholeWeilCarrierEqualityNoLongerLive = Orbit.wholeWeilCarrierEqualityPruned

wholeMellinCarrierEqualityNoLongerLive :
  Orbit.PaymentRelevant Orbit.identifyWholeSourceFunctionSpaceWithMellinTest -> ⊥
wholeMellinCarrierEqualityNoLongerLive = Orbit.wholeMellinCarrierEqualityPruned

genericExplicitFormulaReconstructionNoLongerLive :
  Weld.PaymentRelevant Weld.reconstructGenericExplicitFormula -> ⊥
genericExplicitFormulaReconstructionNoLongerLive =
  Weld.reconstructGenericExplicitFormulaPruned

sameObjectWeldIsCompilerOutput :
  Same.PaymentRelevant Same.weldLiteralSelectedTest -> ⊥
sameObjectWeldIsCompilerOutput = Same.literalSelectedTestWeldAlreadyCompiled

sameObjectNearFarAttachmentIsCompilerOutput :
  Same.PaymentRelevant Same.attachNearFarToSameLiteralTest -> ⊥
sameObjectNearFarAttachmentIsCompilerOutput =
  Same.nearFarSameObjectAttachmentAlreadyCompiled

separateSelectedNearFarSearchNoLongerLive :
  Single.searchStatus Single.separatelyRecoverNearFarWeld ≡ Single.pruned
separateSelectedNearFarSearchNoLongerLive = Single.separateNearFarSearchPruned

separateSelectedSameTestSearchNoLongerLive :
  Single.searchStatus Single.separatelyRecoverSameTestWeld ≡ Single.pruned
separateSelectedSameTestSearchNoLongerLive = Single.separateSameTestSearchPruned

finiteNearCarrierRebuildNoLongerLive :
  NearEval.paymentStatus NearEval.rebuildFiniteNearCarrier ≡ NearEval.pruned
finiteNearCarrierRebuildNoLongerLive = NearEval.finiteCarrierRebuildPruned

farShellReproofNoLongerLive :
  NearEval.paymentStatus NearEval.reproveFarShellDecay ≡ NearEval.pruned
farShellReproofNoLongerLive = NearEval.farShellReproofPruned

cutoffReproofNoLongerLive :
  NearEval.paymentStatus NearEval.reproveArbitraryAccuracyCutoff ≡ NearEval.pruned
cutoffReproofNoLongerLive = NearEval.cutoffReproofPruned

quadraticGapSplitSharpeningNoLongerLive :
  Gap.GapSplitRelevant Gap.sharpenSameQuadraticDecayDonor -> ⊥
quadraticGapSplitSharpeningNoLongerLive = Gap.sameQuadraticDecayDonorPruned

taperGapSplitRetuningNoLongerLive :
  Gap.GapSplitRelevant Gap.retuneTaperWidthOrProfile -> ⊥
taperGapSplitRetuningNoLongerLive = Gap.taperRetuningPruned

coarseCountingClusteringNoLongerLive :
  Gap.GapSplitRelevant Gap.deriveClusteringFromCoarseCountingOnly -> ⊥
coarseCountingClusteringNoLongerLive = Gap.coarseCountingClusteringPruned

genericGammaSearchNoLongerLive :
  PQ.LeafRelevant PQ.findAnyGammaUpperBound -> ⊥
genericGammaSearchNoLongerLive = PQ.findAnyGammaUpperBoundPruned

adaptiveInverseWidthStillLogicallyOpen :
  Gap.densityCutRefutesEveryAdaptiveInverseWidthRoute
    Gap.canonicalGapSplitClusteringLeanReturn8894 ≡ false
adaptiveInverseWidthStillLogicallyOpen =
  Gap.densityCutRefutesEveryAdaptiveInverseWidthRouteIsFalse
    Gap.canonicalGapSplitClusteringLeanReturn8894

------------------------------------------------------------------------
-- Frontier receipt.
------------------------------------------------------------------------

record HighestAlphaAfter8894Boundary : Set where
  constructor highest-alpha-after-8894-boundary
  field
    literalFkSourceMathematicsAlreadyRecovered : Bool
    literalFkSourceMathematicsAlreadyRecoveredIsTrue :
      literalFkSourceMathematicsAlreadyRecovered ≡ true

    actualSelectedPoleNearProducerStillRequired : Bool
    actualSelectedPoleNearProducerStillRequiredIsTrue :
      actualSelectedPoleNearProducerStillRequired ≡ true

    finiteNearCarrierAndFarShellFreshMathematicsRequired : Bool
    finiteNearCarrierAndFarShellFreshMathematicsRequiredIsFalse :
      finiteNearCarrierAndFarShellFreshMathematicsRequired ≡ false

    selectedPhasePreservingFiniteEvaluationStillRequired : Bool
    selectedPhasePreservingFiniteEvaluationStillRequiredIsTrue :
      selectedPhasePreservingFiniteEvaluationStillRequired ≡ true

    evaluatorMustBeWeldedToSelectedWindowFiniteNear : Bool
    evaluatorMustBeWeldedToSelectedWindowFiniteNearIsTrue :
      evaluatorMustBeWeldedToSelectedWindowFiniteNear ≡ true

    sameQuadraticGapSplitRouteStillWorthSharpening : Bool
    sameQuadraticGapSplitRouteStillWorthSharpeningIsFalse :
      sameQuadraticGapSplitRouteStillWorthSharpening ≡ false

    adaptiveConstantWindowComparisonLive : Bool
    adaptiveConstantWindowComparisonLiveIsTrue :
      adaptiveConstantWindowComparisonLive ≡ true

    gammaPrecisionLossLocalizationLive : Bool
    gammaPrecisionLossLocalizationLiveIsTrue :
      gammaPrecisionLossLocalizationLive ≡ true

    gammaPrecisionRepairLive : Bool
    gammaPrecisionRepairLiveIsTrue : gammaPrecisionRepairLive ≡ true

    finalBudgetCombinationAlreadyUnconditional : Bool
    finalBudgetCombinationAlreadyUnconditionalIsFalse :
      finalBudgetCombinationAlreadyUnconditional ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalHighestAlphaAfter8894Boundary : HighestAlphaAfter8894Boundary
canonicalHighestAlphaAfter8894Boundary =
  highest-alpha-after-8894-boundary
    true refl
    true refl
    false refl
    true refl
    true refl
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "PR cross-pollination compresses the zero-side lane to one dependent selected target-window producer followed by one phase-preserving finite-near evaluator on that SAME finite-near scalar. The checked 8883 return already owns the finite near carrier, far-shell modulus/decay, arbitrary-accuracy cutoff and D_off cutoff transport, so rebuilding those is pruned. The live near analysis is to recover an admitted FiniteNearProducer and prove its signedNearValue, after exact scalar-carrier transport, is the finitePoleNearSigned coordinate of the selected PoleNearTargetWindow; its budget extraction is then downstream. The 8894 quadratic gap-split sharpening remains pruned, the adaptive J*Lambda compatibility question remains live, and H_Gamma still requires source-exact precision-loss localization plus repair to the sharp cluster window. RH remains open."
