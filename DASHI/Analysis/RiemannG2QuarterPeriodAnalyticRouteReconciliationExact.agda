module DASHI.Analysis.RiemannG2QuarterPeriodAnalyticRouteReconciliationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2NarrowWindowNoCancellationReturnExact as Narrow
import DASHI.Analysis.RiemannG2CutoffGrowthBidiExact as Growth
import DASHI.Analysis.RiemannG2PoleQuotientProducerReconciliation8889Exact as PQ8889
import DASHI.Analysis.RiemannG2GapSplitClusteringLeanReturn8894Exact as Gap8894
import DASHI.Analysis.RiemannAristotleQuarterPeriodDensityWindowLeanReturnExact as Q37
import DASHI.Analysis.RiemannAristotleZetaLocalCountLeanReturnExact as Z38

------------------------------------------------------------------------
-- QUARTER-PERIOD / ANALYTIC-LEAF RECONCILIATION
--
-- §37 closes the separate J*Lambda constant-window compatibility audit and §38
-- closes zeta upper local counting.
--
-- CORRECTION: the §35 low-gap clustering inequality is necessary for POSITIVITY
-- of the gap-split lower bound used in a no-go against the desired scalar bound.
-- It is therefore retained as an obstruction diagnostic, not a forward RH work
-- package. The forward zero-side theorem remains the consumer-sufficient literal
-- target-centred signed response (the direct finite producer / G2d scalar leaf).
------------------------------------------------------------------------

data AnalyticLeafCode : Set where
  HXcomplexCharacter : AnalyticLeafCode
  HAtestModulationShift : AnalyticLeafCode
  HMassembledModulation : AnalyticLeafCode
  HTtranslationModulation : AnalyticLeafCode
  HWwindowRestriction : AnalyticLeafCode
  HEphaseSensitiveFiniteNearEvaluation : AnalyticLeafCode
  HGammaPrecision : AnalyticLeafCode


data RegimeDependency : Set where
  regimeIndependentInfrastructure : RegimeDependency
  quarterPeriodSensitiveConsumer : RegimeDependency
  deterministicComplementPrecision : RegimeDependency


regimeClass : AnalyticLeafCode -> RegimeDependency
regimeClass HXcomplexCharacter = regimeIndependentInfrastructure
regimeClass HAtestModulationShift = regimeIndependentInfrastructure
regimeClass HMassembledModulation = regimeIndependentInfrastructure
regimeClass HTtranslationModulation = regimeIndependentInfrastructure
regimeClass HWwindowRestriction = regimeIndependentInfrastructure
regimeClass HEphaseSensitiveFiniteNearEvaluation = quarterPeriodSensitiveConsumer
regimeClass HGammaPrecision = deterministicComplementPrecision

record CrossBranchAnalyticFrontierReturn : Set where
  constructor cross-branch-analytic-frontier-return
  field
    sourceBranch : String
    sourceHead : String
    importedAsProofTermsHere : Bool
    importedAsProofTermsHereIsFalse : importedAsProofTermsHere ≡ false

    HXOpen : Bool
    HXOpenIsTrue : HXOpen ≡ true
    HAOpen : Bool
    HAOpenIsFalse : HAOpen ≡ false
    HMOpen : Bool
    HMOpenIsFalse : HMOpen ≡ false
    HTOpen : Bool
    HTOpenIsFalse : HTOpen ≡ false
    HWOpen : Bool
    HWOpenIsFalse : HWOpen ≡ false
    HEOpen : Bool
    HEOpenIsFalse : HEOpen ≡ false
    HGammaOpen : Bool
    HGammaOpenIsTrue : HGammaOpen ≡ true

    analyticDependencyReference : String

open CrossBranchAnalyticFrontierReturn public

canonicalCrossBranchAnalyticFrontierReturn : CrossBranchAnalyticFrontierReturn
canonicalCrossBranchAnalyticFrontierReturn =
  cross-branch-analytic-frontier-return
    "PR #677 agent/aristotle-experimental-proof-search"
    "10a008594ae759cb47bd96f48b88aad34bb1a8a3"
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    "Historical explicit-formula dependency: H_X -> H_A -> H_M -> H_T -> H_W/H_E, with H_Gamma independent. The later direct literal signed route is a separate route and is not blocked on this chain."

CanAdvanceBeforeCrossing : AnalyticLeafCode -> Set
CanAdvanceBeforeCrossing HXcomplexCharacter = ⊤
CanAdvanceBeforeCrossing HAtestModulationShift = ⊤
CanAdvanceBeforeCrossing HMassembledModulation = ⊤
CanAdvanceBeforeCrossing HTtranslationModulation = ⊤
CanAdvanceBeforeCrossing HWwindowRestriction = ⊤
CanAdvanceBeforeCrossing HEphaseSensitiveFiniteNearEvaluation = ⊥
CanAdvanceBeforeCrossing HGammaPrecision = ⊤

phaseEvaluationCannotCloseBeforeCrossing :
  CanAdvanceBeforeCrossing HEphaseSensitiveFiniteNearEvaluation -> ⊥
phaseEvaluationCannotCloseBeforeCrossing x = x

quarterPeriodCrossingNecessaryForCancellation :
  Narrow.survivingRouteRequiresQuarterPeriodCrossing
    Narrow.canonicalNarrowWindowNoCancellationReturn ≡ true
quarterPeriodCrossingNecessaryForCancellation =
  Narrow.survivingRouteRequiresQuarterPeriodCrossingIsTrue
    Narrow.canonicalNarrowWindowNoCancellationReturn

currentCutoffStageStillRequiresCrossing :
  Growth.currentCutoffGrowthStage ≡ Growth.crossingLawRequired
currentCutoffStageStillRequiresCrossing = refl

clusterFreshDerivationPrunedBy8889 :
  PQ8889.LeafRelevant PQ8889.deriveFreshClusterMargin -> ⊥
clusterFreshDerivationPrunedBy8889 = PQ8889.deriveFreshClusterMarginPruned

genericGammaSearchPrunedBy8889 :
  PQ8889.LeafRelevant PQ8889.findAnyGammaUpperBound -> ⊥
genericGammaSearchPrunedBy8889 = PQ8889.findAnyGammaUpperBoundPruned

quadraticDecayGapSplitSharpeningPrunedBy8894 :
  Gap8894.GapSplitRelevant Gap8894.sharpenSameQuadraticDecayDonor -> ⊥
quadraticDecayGapSplitSharpeningPrunedBy8894 = Gap8894.sameQuadraticDecayDonorPruned

taperRetuningGapSplitPrunedBy8894 :
  Gap8894.GapSplitRelevant Gap8894.retuneTaperWidthOrProfile -> ⊥
taperRetuningGapSplitPrunedBy8894 = Gap8894.taperRetuningPruned

coarseCountingClusteringPrunedBy8894 :
  Gap8894.GapSplitRelevant Gap8894.deriveClusteringFromCoarseCountingOnly -> ⊥
coarseCountingClusteringPrunedBy8894 = Gap8894.coarseCountingClusteringPruned

quarterDensityComparisonPrunedBy8896 :
  Gap8894.GapSplitRelevant Gap8894.compareQuarterPeriodLowerConstantWithDensityUpperConstant -> ⊥
quarterDensityComparisonPrunedBy8896 = Gap8894.quarterDensityConstantComparisonPruned

zetaUpperCountSearchPrunedBy8896 :
  Gap8894.GapSplitRelevant Gap8894.recoverZetaUpperLocalCount -> ⊥
zetaUpperCountSearchPrunedBy8896 = Gap8894.zetaUpperLocalCountSearchPruned

quarterDensityNatWindowChecked :
  Q37.explicitIntegerCutoffExistenceOwnedInLean
    Q37.canonicalQuarterPeriodDensityWindowReturn ≡ true
quarterDensityNatWindowChecked = refl

zetaShortWindowUpperCountChecked :
  Z38.zetaShortWindowUpperCountOwnedInLean Z38.canonicalZetaLocalCountLeanReturn ≡ true
zetaShortWindowUpperCountChecked = refl

adaptiveInverseWidthRouteNotRefutedByDensityCut :
  Gap8894.densityCutRefutesEveryAdaptiveInverseWidthRoute
    Gap8894.canonicalGapSplitClusteringLeanReturn8894 ≡ false
adaptiveInverseWidthRouteNotRefutedByDensityCut =
  Gap8894.densityCutRefutesEveryAdaptiveInverseWidthRouteIsFalse
    Gap8894.canonicalGapSplitClusteringLeanReturn8894

clusteringDoesNotDirectlyPayRH :
  Gap8894.clusteringDirectlyPaysRHScalarConsumer
    Gap8894.canonicalGapSplitClusteringLeanReturn8894 ≡ false
clusteringDoesNotDirectlyPayRH = Gap8894.clusteringDoesNotDirectlyPayRH

------------------------------------------------------------------------
-- Work packages after the corrected §35 interpretation.
------------------------------------------------------------------------

data LiveWorkPackage : Set where
  widthAndCrossingScale : LiveWorkPackage
  actualZetaLowGapClustering : LiveWorkPackage
  literalDirectSignedProducer : LiveWorkPackage
  canonicalCharacterInfrastructure : LiveWorkPackage
  gammaPrecisionRepair : LiveWorkPackage
  crossedRegimeFiniteEvaluation : LiveWorkPackage
  finalIndependentBudgetCombination : LiveWorkPackage

data WorkState : Set where
  closed : WorkState
  live : WorkState
  blocked : WorkState
  conditional : WorkState
  diagnostic : WorkState

workState : LiveWorkPackage -> WorkState
workState widthAndCrossingScale = closed
workState actualZetaLowGapClustering = diagnostic
workState literalDirectSignedProducer = live
workState canonicalCharacterInfrastructure = live
workState gammaPrecisionRepair = live
workState crossedRegimeFiniteEvaluation = blocked
workState finalIndependentBudgetCombination = conditional

widthAndCrossingScaleClosed : workState widthAndCrossingScale ≡ closed
widthAndCrossingScaleClosed = refl

actualZetaClusteringIsDiagnostic :
  workState actualZetaLowGapClustering ≡ diagnostic
actualZetaClusteringIsDiagnostic = refl

literalDirectSignedProducerIsLive :
  workState literalDirectSignedProducer ≡ live
literalDirectSignedProducerIsLive = refl

record CrossBranchRegimeReconciliationBoundary : Set where
  constructor cross-branch-regime-reconciliation-boundary
  field
    characterInfrastructureMustWaitForQuarterPeriodCrossing : Bool
    characterInfrastructureMustWaitForQuarterPeriodCrossingIsFalse :
      characterInfrastructureMustWaitForQuarterPeriodCrossing ≡ false

    gammaPrecisionMustWaitForQuarterPeriodCrossing : Bool
    gammaPrecisionMustWaitForQuarterPeriodCrossingIsFalse :
      gammaPrecisionMustWaitForQuarterPeriodCrossing ≡ false

    phaseSensitiveFiniteEvaluationCanCloseInPinnedNarrowRegime : Bool
    phaseSensitiveFiniteEvaluationCanCloseInPinnedNarrowRegimeIsFalse :
      phaseSensitiveFiniteEvaluationCanCloseInPinnedNarrowRegime ≡ false

    widthCrossingConstantComparisonClosedBy8896 : Bool
    widthCrossingConstantComparisonClosedBy8896IsTrue :
      widthCrossingConstantComparisonClosedBy8896 ≡ true

    actualZetaClusteringStillUnproved : Bool
    actualZetaClusteringStillUnprovedIsTrue : actualZetaClusteringStillUnproved ≡ true

    actualZetaClusteringIsForwardRHWorkPackage : Bool
    actualZetaClusteringIsForwardRHWorkPackageIsFalse :
      actualZetaClusteringIsForwardRHWorkPackage ≡ false

    literalDirectSignedProducerForwardLeafOpen : Bool
    literalDirectSignedProducerForwardLeafOpenIsTrue :
      literalDirectSignedProducerForwardLeafOpen ≡ true

    arbitraryGammaUpperBoundNeedsFreshSearch : Bool
    arbitraryGammaUpperBoundNeedsFreshSearchIsFalse :
      arbitraryGammaUpperBoundNeedsFreshSearch ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalCrossBranchRegimeReconciliationBoundary : CrossBranchRegimeReconciliationBoundary
canonicalCrossBranchRegimeReconciliationBoundary =
  cross-branch-regime-reconciliation-boundary
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
    "§37 closes the J*Lambda compatibility audit and §38 closes zeta upper local counting. The §35 clustering condition remains mathematically unproved but belongs to the gap-split positivity/no-go diagnostic, not the forward RH queue. The live forward zero-side payment is the literal target-centred signed scalar theorem packaged as a consumer-sufficient DirectFinitePoleNearProducer. The historical explicit-formula character/modulation route and Gamma precision remain separate alternatives/dependencies. RH is not derived."
