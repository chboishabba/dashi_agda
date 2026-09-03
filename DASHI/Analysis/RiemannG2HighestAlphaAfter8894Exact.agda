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
import DASHI.Analysis.RiemannG2PoleQuotientProducerReconciliation8889Exact as PQ

------------------------------------------------------------------------
-- HIGHEST-ALPHA SCHEDULER AFTER 8894 + CHECKED f_k SOURCE RECOVERY
--
-- Cross-PR BIDI compression now removes a further false decomposition.  PR #691
-- showed that theorem consequences indexed by one literal source producer should
-- not be searched independently.  PR #684 showed that same-object premises can
-- make an apparent physical leaf compiler output.  Applied here, the selected
-- orbit attachment, target-window decomposition, selected same-object weld and
-- selected near/far weld are projections of one dependent target-window producer.
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

separateSelectedNearFarSearchNoLongerLive :
  Single.searchStatus Single.separatelyRecoverNearFarWeld ≡ Single.pruned
separateSelectedNearFarSearchNoLongerLive = Single.separateNearFarSearchPruned

separateSelectedSameTestSearchNoLongerLive :
  Single.searchStatus Single.separatelyRecoverSameTestWeld ≡ Single.pruned
separateSelectedSameTestSearchNoLongerLive = Single.separateSameTestSearchPruned

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

    selectedOrbitWindowAndSameObjectAreIndependentLeaves : Bool
    selectedOrbitWindowAndSameObjectAreIndependentLeavesIsFalse :
      selectedOrbitWindowAndSameObjectAreIndependentLeaves ≡ false

    actualSelectedPoleNearProducerStillRequired : Bool
    actualSelectedPoleNearProducerStillRequiredIsTrue :
      actualSelectedPoleNearProducerStillRequired ≡ true

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
    false refl
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl
    "Recent PR inspiration compresses the selected zero-side lane again. Do not separately recover a source-orbit attachment, a selected same-test weld and a selected near/far weld. Recover one ActualSelectedPoleNearProducer indexed by the same Weil space/formula/orbit: it contains the chosen source attachment, one theorem-bearing PoleNearTargetWindow, equality of their selected Test and the preservation receipts. Existing compilers then generate the literal selected-test weld, same-formula cluster/finite-near/far weld and same-object near/far attachment. In parallel compare the adaptive J*Lambda window or find a different signed mechanism, repair Gamma precision, attach the owned cluster margin and pay the final independent budget inequality. RH remains open."
