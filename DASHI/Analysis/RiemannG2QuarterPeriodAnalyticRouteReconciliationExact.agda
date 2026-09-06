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
-- The earlier owner correctly separated regime-independent infrastructure from
-- the quarter-period-sensitive finite-near consumer.  The checked §37 return
-- now closes the separate width/crossing constant-window audit: it proves exact
-- compatibility arithmetic and Nat cutoff existence under its hypotheses.
-- §38 additionally supplies zeta's upper local count.
--
-- Therefore widthAndCrossingScale is no longer a live work package.  This file
-- is updated in place so downstream schedulers see the closure through the same
-- owner.  The genuinely new analytic payment is actual-zeta low-gap clustering;
-- finite-near evaluation and Gamma precision remain independent existing lanes.
------------------------------------------------------------------------

data AnalyticLeafCode : Set where
  HXcomplexCharacter
  HAtestModulationShift
  HMassembledModulation
  HTtranslationModulation
  HWwindowRestriction
  HEphaseSensitiveFiniteNearEvaluation
  HGammaPrecision
  : AnalyticLeafCode

data RegimeDependency : Set where
  regimeIndependentInfrastructure
  quarterPeriodSensitiveConsumer
  deterministicComplementPrecision
  : RegimeDependency

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
    "Reported dependency: H_X -> H_A -> H_M -> H_T -> direct phase statistic -> H_E, with H_T -> H_W -> explicit window -> H_E and H_Gamma feeding the final consumer independently."

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

-- Historical pre-§37 growth owner: this remains true of that owner's local
-- state, but the later checked producer discharges the corresponding global
-- scheduling leaf below.
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
quadraticDecayGapSplitSharpeningPrunedBy8894 =
  Gap8894.sameQuadraticDecayDonorPruned

taperRetuningGapSplitPrunedBy8894 :
  Gap8894.GapSplitRelevant Gap8894.retuneTaperWidthOrProfile -> ⊥
taperRetuningGapSplitPrunedBy8894 = Gap8894.taperRetuningPruned

coarseCountingClusteringPrunedBy8894 :
  Gap8894.GapSplitRelevant Gap8894.deriveClusteringFromCoarseCountingOnly -> ⊥
coarseCountingClusteringPrunedBy8894 = Gap8894.coarseCountingClusteringPruned

quarterDensityComparisonPrunedBy8896 :
  Gap8894.GapSplitRelevant
    Gap8894.compareQuarterPeriodLowerConstantWithDensityUpperConstant -> ⊥
quarterDensityComparisonPrunedBy8896 = Gap8894.quarterDensityConstantComparisonPruned

zetaUpperCountSearchPrunedBy8896 :
  Gap8894.GapSplitRelevant Gap8894.recoverZetaUpperLocalCount -> ⊥
zetaUpperCountSearchPrunedBy8896 = Gap8894.zetaUpperLocalCountSearchPruned

quarterDensityNatWindowChecked :
  Q37.explicitIntegerCutoffExistenceOwnedInLean
    Q37.canonicalQuarterPeriodDensityWindowReturn ≡ true
quarterDensityNatWindowChecked = refl

zetaShortWindowUpperCountChecked :
  Z38.zetaShortWindowUpperCountOwnedInLean Z38.canonicalZetaLocalCountLeanReturn
  ≡ true
zetaShortWindowUpperCountChecked = refl

adaptiveInverseWidthRouteNotRefutedByDensityCut :
  Gap8894.densityCutRefutesEveryAdaptiveInverseWidthRoute
    Gap8894.canonicalGapSplitClusteringLeanReturn8894 ≡ false
adaptiveInverseWidthRouteNotRefutedByDensityCut =
  Gap8894.densityCutRefutesEveryAdaptiveInverseWidthRouteIsFalse
    Gap8894.canonicalGapSplitClusteringLeanReturn8894

------------------------------------------------------------------------
-- Parallel live work packages after 8896.
------------------------------------------------------------------------

data LiveWorkPackage : Set where
  widthAndCrossingScale
  actualZetaLowGapClustering
  canonicalCharacterInfrastructure
  gammaPrecisionRepair
  crossedRegimeFiniteEvaluation
  finalIndependentBudgetCombination
  : LiveWorkPackage

data WorkState : Set where
  closed live blocked conditional : WorkState

workState : LiveWorkPackage -> WorkState
workState widthAndCrossingScale = closed
workState actualZetaLowGapClustering = live
workState canonicalCharacterInfrastructure = live
workState gammaPrecisionRepair = live
workState crossedRegimeFiniteEvaluation = blocked
workState finalIndependentBudgetCombination = conditional

widthAndCrossingScaleClosed : workState widthAndCrossingScale ≡ closed
widthAndCrossingScaleClosed = refl

actualZetaClusteringIsLive : workState actualZetaLowGapClustering ≡ live
actualZetaClusteringIsLive = refl

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

    actualZetaClusteringStillOpen : Bool
    actualZetaClusteringStillOpenIsTrue : actualZetaClusteringStillOpen ≡ true

    arbitraryGammaUpperBoundNeedsFreshSearch : Bool
    arbitraryGammaUpperBoundNeedsFreshSearchIsFalse :
      arbitraryGammaUpperBoundNeedsFreshSearch ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalCrossBranchRegimeReconciliationBoundary :
  CrossBranchRegimeReconciliationBoundary
canonicalCrossBranchRegimeReconciliationBoundary =
  cross-branch-regime-reconciliation-boundary
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    "The checked §37 return closes the literal J*Lambda lower-versus-upper constant-window audit, including Nat cutoff existence, and §38 closes zeta upper local counting. Those are no longer parallel search packages. The gap-split owner now routes directly to actual-zeta low-gap clustering. Character/modulation infrastructure, the existing same-object finite-near evaluator, and Gamma precision remain separate genuine dependencies. No checked return here supplies the clustering inequality or RH."
