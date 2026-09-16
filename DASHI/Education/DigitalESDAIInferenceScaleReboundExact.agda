module DASHI.Education.DigitalESDAIInferenceScaleReboundExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone

------------------------------------------------------------------------
-- AI INFERENCE SCALE / REBOUND CALIBRATION
--
-- This owner is a technical calibration donor for digital-ESD material impact.
-- It does not turn a general AI-inference model into an education-specific
-- deployment footprint. In particular, scenario-demonstrated demand growth is
-- not mislabeled as an empirically observed rebound time series.
------------------------------------------------------------------------

oviedoInferenceEnergySource : Attr.AttributedSource
oviedoInferenceEnergySource =
  Attr.mkDOISource
    "Felipe Oviedo; Fiodar Kazhamiaka; Esha Choukse; Allen Kim; Amy Luers; Melanie Nakagawa; Ricardo Bianchini; Juan M. Lavista Ferres"
    "Energy use of AI inference, efficiency pathways, and test-time scaling"
    "Joule"
    "2026"
    "10.1016/j.joule.2026.102430"
    "https://doi.org/10.1016/j.joule.2026.102430"
    Attr.academicArticleSource
    "Peer-reviewed bottom-up AI-inference energy model calibrated to production-scale disclosures/benchmarks. It supports bounded statements about per-query energy, test-time-scaling sensitivity and aggregate demand scenarios; it is not an education-specific lifecycle inventory and does not by itself observe a historical rebound response to falling per-query energy."
    Attr.publicAttribution

standardQueryMedianWh : String
standardQueryMedianWh = "0.31 Wh/query"

standardQueryIQR : String
standardQueryIQR = "IQR 0.16-0.60 Wh/query"

longQueryMedianWh : String
longQueryMedianWh = "3.91 Wh/query"

longQueryIQR : String
longQueryIQR = "IQR 2.15-7.05 Wh/query"

oneBillionQueriesPerDayBaseline : String
oneBillionQueriesPerDayBaseline = "0.7 GWh/day"

oneBillionQueriesTenPercentLong : String
oneBillionQueriesTenPercentLong = "1.7 GWh/day"

oneBillionQueriesEfficiencyScenario : String
oneBillionQueriesEfficiencyScenario = "0.8 GWh/day"

lineOfSightEfficiencyRange : String
lineOfSightEfficiencyRange = "8-20x modeled per-query energy reduction across model, serving and hardware interventions"

oviedoScope : PNF.AssertionScope
oviedoScope = PNF.assertionScope
  "frontier-scale LLM inference workloads under the source's production-scale serving assumptions"
  "modeled H100-node / large-scale serving context aligned to public production disclosures and throughput benchmarks"
  "standard-query and test-time-scaling inference workloads"
  "standard-query workload versus approximately 15x longer reasoning/test-time-scaling workload; aggregate scenarios also vary long-query share and efficiency interventions"
  "electricity use per query and aggregate daily inference electricity demand"
  "modeled deployment scenarios, not a longitudinal historical demand panel"

oviedoPredicates : List PNF.PredicateAtom
oviedoPredicates =
  PNF.predicateAtom "standard-query-energy" PNF.outcomePredicate "query × Wh"
    "source estimates median frontier-scale standard-query energy at 0.31 Wh/query with IQR 0.16-0.60"
  ∷ PNF.predicateAtom "long-query-energy" PNF.outcomePredicate "reasoning-query × Wh"
    "approximately 15x longer test-time-scaling workload raises modeled median energy to 3.91 Wh/query with IQR 2.15-7.05, about 13x the standard-query median"
  ∷ PNF.predicateAtom "aggregate-volume-scenario" PNF.contextPredicate "queries-per-day × workload-mix"
    "at one billion queries/day the baseline modeled demand is 0.7 GWh/day; with 10% long reasoning queries it rises to 1.7 GWh/day"
  ∷ PNF.predicateAtom "efficiency-stack-scenario" PNF.contextPredicate "model × serving × hardware"
    "source estimates 8-20x line-of-sight per-query efficiency potential; an illustrative one-billion-query/day efficiency scenario yields 0.8 GWh/day"
  ∷ PNF.predicateAtom "demand-dynamics-residual" PNF.contextPredicate "efficiency × usage"
    "the source explicitly notes that lower energy per query or cost per token can enable higher usage, longer generations and more token-intensive workflows, so aggregate outcomes depend jointly on efficiency and demand dynamics"
  ∷ []

oviedoScaleAssertion : PNF.PredicateNormalAssertion
oviedoScaleAssertion = PNF.predicateNormalAssertion
  "oviedo-2026-inference-scale-energy"
  "Under the source's production-scale inference model, long reasoning workloads use substantially more energy per query, and aggregate daily demand can rise materially with query volume and workload mix even when per-query efficiency improves."
  PNF.studyPopulationQ
  PNF.comparativeF
  oviedoScope
  oviedoPredicates
  "same-object DOI 10.1016/j.joule.2026.102430; modeled medians/IQRs and billion-query/day scenarios retained with their workload/serving assumptions"

oviedoStrongestPaidImplication : Cone.ImplicationKind
oviedoStrongestPaidImplication = Cone.derivesBoundedContrast

oviedoFirstUnpaidImplication : Cone.ImplicationKind
oviedoFirstUnpaidImplication = Cone.transportsPopulation

reboundStatusReading : String
reboundStatusReading =
  "The source directly pays a scale-sensitivity counterexample to the naive inference that lower per-query energy guarantees lower aggregate inference energy. It does not, however, observe a longitudinal causal rebound elasticity after an efficiency change. Therefore the review may say aggregate demand depends jointly on per-query efficiency and demand/workload dynamics, but may not label the modeled scenarios an empirically measured rebound effect."

educationTransferReading : String
educationTransferReading =
  "Oviedo et al. is a technical AI-inference calibration source. It can constrain the digital-ESD material model by showing workload length, serving efficiency, utilization and query volume matter. It cannot supply the workload mix, provider route, grid mix, hardware lifecycle allocation or aggregate demand of a named educational AI deployment. Those remain same-object deployment obligations."

------------------------------------------------------------------------
-- Non-promotion firewalls.
------------------------------------------------------------------------

data LowerPerQueryEnergyCreatesLowerAggregateEnergy : Set where
data ModeledDemandScenarioCreatesObservedRebound : Set where
data GeneralInferenceModelCreatesEducationDeploymentFootprint : Set where

lowerPerQueryEnergyDoesNotCreateLowerAggregateEnergy : LowerPerQueryEnergyCreatesLowerAggregateEnergy → ⊥
lowerPerQueryEnergyDoesNotCreateLowerAggregateEnergy ()

modeledDemandScenarioDoesNotCreateObservedRebound : ModeledDemandScenarioCreatesObservedRebound → ⊥
modeledDemandScenarioDoesNotCreateObservedRebound ()

generalInferenceModelDoesNotCreateEducationDeploymentFootprint :
  GeneralInferenceModelCreatesEducationDeploymentFootprint → ⊥
generalInferenceModelDoesNotCreateEducationDeploymentFootprint ()
