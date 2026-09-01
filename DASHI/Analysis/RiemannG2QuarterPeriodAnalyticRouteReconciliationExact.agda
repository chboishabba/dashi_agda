module DASHI.Analysis.RiemannG2QuarterPeriodAnalyticRouteReconciliationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2NarrowWindowNoCancellationReturnExact as Narrow
import DASHI.Analysis.RiemannG2CutoffGrowthBidiExact as Growth
import DASHI.Analysis.RiemannG2PoleQuotientProducerReconciliation8889Exact as PQ8889

------------------------------------------------------------------------
-- QUARTER-PERIOD / ANALYTIC-LEAF RECONCILIATION
--
-- A parallel RH branch currently reports the recursive analytic decomposition
--
--   H_X -> H_A -> H_M -> H_T -> H_W -> H_E
--
-- with H_Gamma independent and live in parallel.  This module does not import
-- that open draft branch and does not pretend its Agda proof terms are present
-- here.  It records only the cross-branch frontier correspondence needed to
-- reconcile that decomposition with the checked-Lean 8890 narrow-window no-go
-- already owned on this branch.
--
-- Key correction: quarter-period crossing is necessary for phase cancellation,
-- but it is NOT a prerequisite for constructing regime-independent character,
-- modulation, or Gamma infrastructure.  Therefore H_X and Gamma precision may
-- advance in parallel with the literal Lambda(t)/J(t) scaling audit.  H_E, by
-- contrast, cannot close the unchanged narrow scalar consumer while
-- J*Lambda <= pi/2.
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
    "107436163baf6016f985f6b95fce82460a992cfb"
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    "Reported dependency: H_X -> H_A -> H_M -> H_T -> direct phase statistic -> H_E, with H_T -> H_W -> explicit window -> H_E and H_Gamma feeding the final consumer independently."

------------------------------------------------------------------------
-- What may be worked before quarter-period crossing?
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Parallel live work packages.
------------------------------------------------------------------------

data LiveWorkPackage : Set where
  widthAndCrossingScale
  canonicalCharacterInfrastructure
  gammaPrecisionRepair
  crossedRegimeFiniteEvaluation
  finalIndependentBudgetCombination
  : LiveWorkPackage

data WorkState : Set where
  live blocked conditional : WorkState

workState : LiveWorkPackage -> WorkState
workState widthAndCrossingScale = live
workState canonicalCharacterInfrastructure = live
workState gammaPrecisionRepair = live
workState crossedRegimeFiniteEvaluation = blocked
workState finalIndependentBudgetCombination = conditional

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

    widthCrossingCharacterAndGammaMayAdvanceInParallel : Bool
    widthCrossingCharacterAndGammaMayAdvanceInParallelIsTrue :
      widthCrossingCharacterAndGammaMayAdvanceInParallel ≡ true

    quantitativeClusterNeedsFreshAnalysis : Bool
    quantitativeClusterNeedsFreshAnalysisIsFalse :
      quantitativeClusterNeedsFreshAnalysis ≡ false

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
    false refl
    false refl
    false refl
    "The 8890 no-cancellation theorem and the PR #677 recursive analytic frontier are complementary, not sequential in every coordinate. Build canonical complex-character/modulation infrastructure and repair Gamma precision in parallel with the literal Lambda(t)/J(t) crossing audit. Do not schedule H_E as a cancellation closure on the unchanged problem until pi/2 < J*Lambda. The 8889 return already removes fresh cluster derivation and generic Gamma-bound search: what survives is same-object cluster attachment, sharp Gamma precision repair, crossed-regime signed off-ordinate evaluation, and an independent strict budget combination."
