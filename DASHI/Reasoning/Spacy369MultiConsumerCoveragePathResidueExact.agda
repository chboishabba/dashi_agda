module DASHI.Reasoning.Spacy369MultiConsumerCoveragePathResidueExact where

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Actionability
import DASHI.Reasoning.Spacy369MultiConsumerCoverageChartExact as Coverage
import DASHI.Reasoning.TernaryComparisonSynthesisExact as Synthesis

------------------------------------------------------------------------
-- SEQUENTIAL COVERAGE PATHS + RETAINED PROBE-ORDER RESIDUE.
--
-- This owner stays on the consumer-coverage 27-cell chart.  It does not reuse
-- the parser-review chart as though the coordinates had the same semantics.
-- Two different information-acquisition orders can reach the same terminal
-- coverage chart while retaining distinct audit histories.
------------------------------------------------------------------------

open Coverage using
  (ConsumerCoverageStatus; coverageOpen; coverageSuspended; coverageClosed;
   coverageTrit)

coverageChart :
  ConsumerCoverageStatus →
  ConsumerCoverageStatus →
  ConsumerCoverageStatus →
  Synthesis.SynthesisChoice27
coverageChart subject standing closure =
  Synthesis.makeSynthesisChoice
    (coverageTrit subject)
    (coverageTrit standing)
    (coverageTrit closure)

initialCoverage : Synthesis.SynthesisChoice27
initialCoverage = coverageChart coverageOpen coverageOpen coverageOpen

afterSharedContextProbe : Synthesis.SynthesisChoice27
afterSharedContextProbe =
  coverageChart coverageClosed coverageClosed coverageSuspended

afterClosureOnlyProbe : Synthesis.SynthesisChoice27
afterClosureOnlyProbe =
  coverageChart coverageOpen coverageOpen coverageClosed

fullyClosedCoverage : Synthesis.SynthesisChoice27
fullyClosedCoverage =
  coverageChart coverageClosed coverageClosed coverageClosed

sharedStageMatchesPriorCoverageOwner :
  afterSharedContextProbe ≡ Coverage.sharedProbeCoverageChart
sharedStageMatchesPriorCoverageOwner = refl

------------------------------------------------------------------------
-- Information actions.  Their costs are declared search/resource costs only.
------------------------------------------------------------------------

data CoverageProbe : Set where
  sharedContextProbe closureResidualProbe : CoverageProbe

probeMove : CoverageProbe → Actionability.InformationMove
probeMove sharedContextProbe =
  Actionability.informationMove
    Actionability.takeMeasurement
    2
    "shared subject-position + governed-standing observation"
    "one richer provenance/context acquisition"
    "independent context/provenance authority required"
probeMove closureResidualProbe =
  Actionability.informationMove
    Actionability.takeMeasurement
    1
    "closure/excluded-residual observation"
    "one closure-specific audit acquisition"
    "closure-audit authority required"

------------------------------------------------------------------------
-- Proof-relevant finite path language.
------------------------------------------------------------------------

data CoverageStage : Set where
  startStage sharedStage closureStage terminalStage : CoverageStage

stageChart : CoverageStage → Synthesis.SynthesisChoice27
stageChart startStage = initialCoverage
stageChart sharedStage = afterSharedContextProbe
stageChart closureStage = afterClosureOnlyProbe
stageChart terminalStage = fullyClosedCoverage

data CoverageTransition : CoverageStage → CoverageStage → Set where
  sharedFirst : CoverageTransition startStage sharedStage
  closureAfterShared : CoverageTransition sharedStage terminalStage
  closureFirst : CoverageTransition startStage closureStage
  sharedAfterClosure : CoverageTransition closureStage terminalStage

data CoveragePath : CoverageStage → CoverageStage → Set where
  pathRefl : (stage : CoverageStage) → CoveragePath stage stage
  pathStep :
    ∀ {a b c} →
    CoverageTransition a b →
    CoveragePath b c →
    CoveragePath a c

sharedThenClosure : CoveragePath startStage terminalStage
sharedThenClosure = pathStep sharedFirst (pathStep closureAfterShared (pathRefl terminalStage))

closureThenShared : CoveragePath startStage terminalStage
closureThenShared = pathStep closureFirst (pathStep sharedAfterClosure (pathRefl terminalStage))

sameTerminalCoverage :
  stageChart terminalStage ≡ fullyClosedCoverage
sameTerminalCoverage = refl

------------------------------------------------------------------------
-- Ordered path residue remains distinct despite endpoint reconvergence.
------------------------------------------------------------------------

data ProbeOrderResidue : Set where
  sharedThenClosureResidue closureThenSharedResidue : ProbeOrderResidue

data CoverageHistory : Set where
  historySharedThenClosure historyClosureThenShared : CoverageHistory

terminalObserver : CoverageHistory → Synthesis.SynthesisChoice27
terminalObserver historySharedThenClosure = fullyClosedCoverage
terminalObserver historyClosureThenShared = fullyClosedCoverage

historyResidue : CoverageHistory → ProbeOrderResidue
historyResidue historySharedThenClosure = sharedThenClosureResidue
historyResidue historyClosureThenShared = closureThenSharedResidue

sameTerminalAcrossProbeOrders :
  terminalObserver historySharedThenClosure
  ≡ terminalObserver historyClosureThenShared
sameTerminalAcrossProbeOrders = refl

probeOrderResiduesDiffer :
  historyResidue historySharedThenClosure
  ≡ historyResidue historyClosureThenShared → ⊥
probeOrderResiduesDiffer ()

terminalCoverageCannotRecoverProbeOrder :
  INF.FactorsThrough terminalObserver historyResidue → ⊥
terminalCoverageCannotRecoverProbeOrder =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      historySharedThenClosure
      historyClosureThenShared
      sameTerminalAcrossProbeOrders
      probeOrderResiduesDiffer)

------------------------------------------------------------------------
-- The intermediate states differ too.  One route first closes subject/standing
-- and leaves closure suspended; the other first closes only closure.
------------------------------------------------------------------------

sharedAndClosureIntermediateChartsDiffer :
  afterSharedContextProbe ≡ afterClosureOnlyProbe → ⊥
sharedAndClosureIntermediateChartsDiffer same =
  highNotLow (cong proj₁ same)
  where
    highNotLow : Base.tri-high ≡ Base.tri-low → ⊥
    highNotLow ()

------------------------------------------------------------------------
-- Cross-domain boundaries.
------------------------------------------------------------------------

record Spacy369MultiConsumerCoveragePathResidueBoundary : Set where
  constructor spacy369MultiConsumerCoveragePathResidueBoundary
  field
    distinctProbeOrdersMayReachSameTerminalCoverage : Bool
    distinctProbeOrdersMayReachSameTerminalCoverageIsTrue :
      distinctProbeOrdersMayReachSameTerminalCoverage ≡ true
    terminalCoverageRecoversProbeOrder : Bool
    terminalCoverageRecoversProbeOrderIsFalse :
      terminalCoverageRecoversProbeOrder ≡ false
    intermediateCoverageNeedBeSameAcrossProbeOrders : Bool
    intermediateCoverageNeedBeSameAcrossProbeOrdersIsFalse :
      intermediateCoverageNeedBeSameAcrossProbeOrders ≡ false
    informationMoveCostIsWelfareMetric : Bool
    informationMoveCostIsWelfareMetricIsFalse :
      informationMoveCostIsWelfareMetric ≡ false
    informationMoveCostCreatesEpistemicAuthority : Bool
    informationMoveCostCreatesEpistemicAuthorityIsFalse :
      informationMoveCostCreatesEpistemicAuthority ≡ false
    sameTerminal369CellMeansSameHistoricalPath : Bool
    sameTerminal369CellMeansSameHistoricalPathIsFalse :
      sameTerminal369CellMeansSameHistoricalPath ≡ false

canonicalSpacy369MultiConsumerCoveragePathResidueBoundary :
  Spacy369MultiConsumerCoveragePathResidueBoundary
canonicalSpacy369MultiConsumerCoveragePathResidueBoundary =
  spacy369MultiConsumerCoveragePathResidueBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
