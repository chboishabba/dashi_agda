module DASHI.Core.ResidualConditionedExperimentPortfolioExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Core.ExpectedFibreReductionCostExact as Reduction
import DASHI.Core.ResidualLiveSetSalienceSchedulerBidiExact as Live

------------------------------------------------------------------------
-- RESIDUAL-CONDITIONED EXPERIMENT PORTFOLIO
--
-- A portfolio is indexed by the current live fibre and residual context.
-- Stale experiments may remain historically valid while losing next-step
-- salience once they no longer split any live, consumer-relevant worlds.
------------------------------------------------------------------------

record ExperimentPortfolio : Set₁ where
  constructor experimentPortfolio
  field
    Experiment : Set
    ResidualContext : Set
    Consumer : Set
    Authority : Set

    move : Experiment → Choice.InformationMove
    reduction : Experiment → Reduction.ReductionEnvelope
    relevantNow : ResidualContext → Consumer → Experiment → Bool
    admissibleNow : Authority → Experiment → Bool
    experimentReference : Experiment → String

open ExperimentPortfolio public

record PortfolioCandidate
    (P : ExperimentPortfolio)
    (residual : ResidualContext P)
    (consumer : Consumer P)
    (authority : Authority P)
    (experiment : Experiment P) : Set where
  constructor portfolioCandidate
  field
    relevant : relevantNow P residual consumer experiment ≡ true
    admissible : admissibleNow P authority experiment ≡ true
    liveSetDiscriminationReference : String
    reductionCostReference : String

open PortfolioCandidate public

record ResidualConditionedSelection
    (P : ExperimentPortfolio)
    (residual : ResidualContext P)
    (consumer : Consumer P)
    (authority : Authority P) : Set₁ where
  constructor residualConditionedSelection
  field
    selected : Experiment P
    selectedReceipt : PortfolioCandidate P residual consumer authority selected
    rejectedStaleReference : String
    comparisonReference : String

open ResidualConditionedSelection public

------------------------------------------------------------------------
-- Exact finite fixture: chemistry may be high value at t0 and stale at t1,
-- while a downstream discriminator becomes the preferred next experiment.
------------------------------------------------------------------------

data ToyExperiment : Set where chemistryProbe downstreamProbe : ToyExperiment
data ToyResidual : Set where chemistryUnresolved chemistryResolvedDownstreamLive : ToyResidual
data ToyConsumer : Set where mechanismConsumer : ToyConsumer
data ToyAuthority : Set where measurementAuthority : ToyAuthority

toyMove : ToyExperiment → Choice.InformationMove
toyMove chemistryProbe = Choice.informationMove Choice.takeMeasurement 1 "chemistry probe" "toy" "admitted"
toyMove downstreamProbe = Choice.informationMove Choice.takeMeasurement 2 "downstream probe" "toy" "admitted"

toyReduction : ToyExperiment → Reduction.ReductionEnvelope
toyReduction chemistryProbe = Reduction.reductionEnvelope 1 2 "chemistry can reduce initial fibre"
toyReduction downstreamProbe = Reduction.reductionEnvelope 1 1 "downstream probe splits remaining collision"

toyRelevant : ToyResidual → ToyConsumer → ToyExperiment → Bool
toyRelevant chemistryUnresolved mechanismConsumer chemistryProbe = true
toyRelevant chemistryUnresolved mechanismConsumer downstreamProbe = false
toyRelevant chemistryResolvedDownstreamLive mechanismConsumer chemistryProbe = false
toyRelevant chemistryResolvedDownstreamLive mechanismConsumer downstreamProbe = true

toyAdmissible : ToyAuthority → ToyExperiment → Bool
toyAdmissible measurementAuthority _ = true

toyRef : ToyExperiment → String
toyRef chemistryProbe = "upstream chemistry discriminator"
toyRef downstreamProbe = "downstream function/recovery/regulatory discriminator"

toyPortfolio : ExperimentPortfolio
toyPortfolio = experimentPortfolio
  ToyExperiment ToyResidual ToyConsumer ToyAuthority
  toyMove toyReduction toyRelevant toyAdmissible toyRef

initialChemistryCandidate :
  PortfolioCandidate toyPortfolio chemistryUnresolved mechanismConsumer measurementAuthority chemistryProbe
initialChemistryCandidate = portfolioCandidate refl refl
  "chemistry still separates live worlds"
  "declared upstream reduction envelope"

laterDownstreamCandidate :
  PortfolioCandidate toyPortfolio chemistryResolvedDownstreamLive mechanismConsumer measurementAuthority downstreamProbe
laterDownstreamCandidate = portfolioCandidate refl refl
  "after chemistry closure, downstream probe separates the remaining collision"
  "declared downstream reduction envelope"

initialSelection :
  ResidualConditionedSelection toyPortfolio chemistryUnresolved mechanismConsumer measurementAuthority
initialSelection = residualConditionedSelection
  chemistryProbe initialChemistryCandidate
  "downstream probe not yet salient"
  "select current live-fibre discriminator"

laterSelection :
  ResidualConditionedSelection toyPortfolio chemistryResolvedDownstreamLive mechanismConsumer measurementAuthority
laterSelection = residualConditionedSelection
  downstreamProbe laterDownstreamCandidate
  "chemistry remains historical evidence but is stale as a next discriminator"
  "select probe that splits the remaining live fibre"

selectionChangesAfterResidualUpdate :
  selected initialSelection ≡ selected laterSelection → ⊥
selectionChangesAfterResidualUpdate ()

record ResidualConditionedPortfolioBoundary : Set where
  constructor residualConditionedPortfolioBoundary
  field
    onceUsefulExperimentAlwaysHighestSalience : Bool
    onceUsefulExperimentAlwaysHighestSalienceIsFalse : onceUsefulExperimentAlwaysHighestSalience ≡ false
    retainedEvidenceForcesRepeatMeasurement : Bool
    retainedEvidenceForcesRepeatMeasurementIsFalse : retainedEvidenceForcesRepeatMeasurement ≡ false
    residualUpdateMayChangeSelectedExperiment : Bool
    residualUpdateMayChangeSelectedExperimentIsTrue : residualUpdateMayChangeSelectedExperiment ≡ true
    portfolioSelectionCreatesExecutionAuthority : Bool
    portfolioSelectionCreatesExecutionAuthorityIsFalse : portfolioSelectionCreatesExecutionAuthority ≡ false

canonicalResidualConditionedPortfolioBoundary : ResidualConditionedPortfolioBoundary
canonicalResidualConditionedPortfolioBoundary =
  residualConditionedPortfolioBoundary false refl false refl true refl false refl

existingLiveSetBoundary : Live.ResidualLiveSetSalienceBoundary
existingLiveSetBoundary = Live.canonicalResidualLiveSetSalienceBoundary
