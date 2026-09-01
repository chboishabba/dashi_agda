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
import DASHI.Analysis.RiemannG2PoleQuotientProducerReconciliation8889Exact as PQ

------------------------------------------------------------------------
-- HIGHEST-ALPHA SCHEDULER AFTER 8894 + CHECKED f_k SOURCE RECOVERY
--
-- Source-side H_A mathematics is paid on the literal f_k family.  The target
-- consumer only needs the selected source orbit embedded into one Weil Test.
-- Cross-pollination from the Moonshine same-element weld then removes another
-- duplicate payment: once FkOrbitConsumerAttachment exists, the literal selected
-- Test, its admissibility, and the fact that the near/far weld uses that same
-- Test are compiler output.  The substantive remaining zero-side theorem is the
-- same-formula spectral near/far equality on that literal selected Test.
------------------------------------------------------------------------

data RH8894Leaf : Set where
  searchForModulationOperation
  rebuildCharacterMultiplication
  identifyWholeSourceFunctionSpaceWithWeilTest
  identifyWholeSourceFunctionSpaceWithMellinTest
  recoverSelectedFkOrbitAttachment
  compileSelectedFkSameObjectWeld
  recoverSelectedSameFormulaNearFarSpectralEquality

  sharpenQuadraticDecayGapSplit
  retuneTaperForGapSplit
  deriveClusteringFromCoarseCounting
  compareAdaptiveJLambdaConstants
  seekDifferentSignedNearMechanism

  searchForAnyGammaBound
  repairGammaToSharpWindow
  attachOwnedClusterMargin
  combineFinalIndependentBudgets
  : RH8894Leaf

data LeafState : Set where
  pruned owned live conditional : LeafState

leafState : RH8894Leaf -> LeafState
leafState searchForModulationOperation = owned
leafState rebuildCharacterMultiplication = pruned
leafState identifyWholeSourceFunctionSpaceWithWeilTest = pruned
leafState identifyWholeSourceFunctionSpaceWithMellinTest = pruned
leafState recoverSelectedFkOrbitAttachment = live
leafState compileSelectedFkSameObjectWeld = owned
leafState recoverSelectedSameFormulaNearFarSpectralEquality = live

leafState sharpenQuadraticDecayGapSplit = pruned
leafState retuneTaperForGapSplit = pruned
leafState deriveClusteringFromCoarseCounting = pruned
leafState compareAdaptiveJLambdaConstants = live
leafState seekDifferentSignedNearMechanism = live

leafState searchForAnyGammaBound = pruned
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

sourceContDiffReproofNoLongerLive :
  FkChecked.FkSourceRelevant FkChecked.reproveSourceContDiff -> ⊥
sourceContDiffReproofNoLongerLive = FkChecked.sourceContDiffReproofPruned

sourceCompactSupportReproofNoLongerLive :
  FkChecked.FkSourceRelevant FkChecked.reproveSourceCompactSupport -> ⊥
sourceCompactSupportReproofNoLongerLive = FkChecked.sourceCompactSupportReproofPruned

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

    wholeSourceFunctionSpaceEqualityRequired : Bool
    wholeSourceFunctionSpaceEqualityRequiredIsFalse :
      wholeSourceFunctionSpaceEqualityRequired ≡ false

    selectedFkOrbitAttachmentStillRequired : Bool
    selectedFkOrbitAttachmentStillRequiredIsTrue :
      selectedFkOrbitAttachmentStillRequired ≡ true

    sameObjectWeldIsSeparatePayment : Bool
    sameObjectWeldIsSeparatePaymentIsFalse :
      sameObjectWeldIsSeparatePayment ≡ false

    sameAgdaExplicitFormulaNearFarEqualityStillRequired : Bool
    sameAgdaExplicitFormulaNearFarEqualityStillRequiredIsTrue :
      sameAgdaExplicitFormulaNearFarEqualityStillRequired ≡ true

    sameQuadraticGapSplitRouteStillWorthSharpening : Bool
    sameQuadraticGapSplitRouteStillWorthSharpeningIsFalse :
      sameQuadraticGapSplitRouteStillWorthSharpening ≡ false

    adaptiveConstantWindowComparisonLive : Bool
    adaptiveConstantWindowComparisonLiveIsTrue :
      adaptiveConstantWindowComparisonLive ≡ true

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
    false refl
    true refl
    false refl
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl
    "Cross-pollinating the Moonshine same-element rule tightens the RH selected-test lane. The checked source already owns fk character multiplication, paperFT shift and analytic prerequisites. Whole source-carrier equality is unnecessary. Recover one consumer-relative FkOrbitConsumerAttachment from the checked source into the chosen Agda Weil Test. From that attachment, the literal selected Test, its admissibility, the arithmetic/spectral paired observation, and same-test near/far attachment are compiler output. Do not schedule them as independent leaves. The substantive zero-side theorem is now the same-RiemannExplicitFormula equality spectralZeroForm(selectedPoleTest) = same-ordinate cluster + finite signed near response + the same far remainder. In parallel compare the adaptive J*Lambda constant window or find a different signed mechanism, repair Gamma precision, attach the owned cluster margin, then pay the final independent budget inequality. RH remains open."
