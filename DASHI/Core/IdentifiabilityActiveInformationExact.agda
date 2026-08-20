module DASHI.Core.IdentifiabilityActiveInformationExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Ranking an explanation is not identification.  This module formalises
-- observational equivalence/equifinality, a distinguishing experiment that
-- splits an equivalence class, and an exact decision-value witness: before the
-- diagnostic observation no one action can be correct for both models, while
-- after it a result-indexed policy is exactly correct.
--
-- REFERENCES / MOTIVATION
--
-- Keith J. Beven,
-- "A manifesto for the equifinality thesis",
-- Journal of Hydrology 320 (2006), 18-36.
-- DOI: 10.1016/j.jhydrol.2005.07.007.
--
-- Byron K. Williams, Mitchell J. Eaton, David R. Breininger,
-- "Adaptive resource management and the value of information",
-- Ecological Modelling 222 (2011), 3429-3436.
-- DOI: 10.1016/j.ecolmodel.2011.07.003.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

record ExperimentSystem (Model Experiment Result : Set) : Set₁ where
  constructor experimentSystem
  field
    observe : Experiment → Model → Result

open ExperimentSystem public

record EquivalentOn
    {Model Experiment Result : Set}
    (system : ExperimentSystem Model Experiment Result)
    (Declared : Experiment → Set)
    (left right : Model) : Set₁ where
  constructor equivalentOn
  field
    agree :
      ∀ experiment →
      Declared experiment →
      observe system experiment left ≡ observe system experiment right

open EquivalentOn public

record DistinguishingExperiment
    {Model Experiment Result : Set}
    (system : ExperimentSystem Model Experiment Result)
    (left right : Model) : Set where
  constructor distinguishingExperiment
  field
    experiment : Experiment
    distinguishes :
      observe system experiment left ≡ observe system experiment right → ⊥

open DistinguishingExperiment public

splitterRefutesAnyFamilyContainingIt :
  ∀ {Model Experiment Result}
    {system : ExperimentSystem Model Experiment Result}
    {left right : Model}
    {Declared : Experiment → Set} →
  (splitter : DistinguishingExperiment system left right) →
  Declared (experiment splitter) →
  EquivalentOn system Declared left right →
  ⊥
splitterRefutesAnyFamilyContainingIt splitter included equivalent =
  distinguishes splitter
    (agree equivalent (experiment splitter) included)

data DemoModel : Set where
  upstreamSource localSource : DemoModel

data DemoExperiment : Set where
  baselineSample diagnosticTracer : DemoExperiment

data DemoResult : Set where
  sameLoad upstreamSignature localSignature : DemoResult

observeDemo : DemoExperiment → DemoModel → DemoResult
observeDemo baselineSample upstreamSource = sameLoad
observeDemo baselineSample localSource = sameLoad
observeDemo diagnosticTracer upstreamSource = upstreamSignature
observeDemo diagnosticTracer localSource = localSignature

demoSystem : ExperimentSystem DemoModel DemoExperiment DemoResult
demoSystem = experimentSystem observeDemo

data BaselineOnly : DemoExperiment → Set where
  baselineDeclared : BaselineOnly baselineSample

baselineEquifinality :
  EquivalentOn demoSystem BaselineOnly upstreamSource localSource
baselineEquifinality = equivalentOn agreement
  where
    agreement :
      ∀ experiment →
      BaselineOnly experiment →
      observeDemo experiment upstreamSource ≡ observeDemo experiment localSource
    agreement baselineSample baselineDeclared = refl

diagnosticDistinguishes :
  DistinguishingExperiment demoSystem upstreamSource localSource
diagnosticDistinguishes = distinguishingExperiment diagnosticTracer impossible
  where
    impossible : upstreamSignature ≡ localSignature → ⊥
    impossible ()

data ManagementAction : Set where
  treatUpstream treatLocal : ManagementAction

requiredAction : DemoModel → ManagementAction
requiredAction upstreamSource = treatUpstream
requiredAction localSource = treatLocal

uniformActionCannotServeBoth :
  ∀ action →
  action ≡ requiredAction upstreamSource →
  action ≡ requiredAction localSource →
  ⊥
uniformActionCannotServeBoth treatUpstream refl ()
uniformActionCannotServeBoth treatLocal () second

informationPolicy : DemoResult → ManagementAction
informationPolicy upstreamSignature = treatUpstream
informationPolicy localSignature = treatLocal
informationPolicy sameLoad = treatUpstream

diagnosticPolicyCorrectUpstream :
  informationPolicy (observeDemo diagnosticTracer upstreamSource)
  ≡ requiredAction upstreamSource
diagnosticPolicyCorrectUpstream = refl

diagnosticPolicyCorrectLocal :
  informationPolicy (observeDemo diagnosticTracer localSource)
  ≡ requiredAction localSource
diagnosticPolicyCorrectLocal = refl

record PositiveDecisionValueWitness : Set where
  constructor positiveDecisionValueWitness
  field
    baselineModelsEquivalent :
      EquivalentOn demoSystem BaselineOnly upstreamSource localSource
    noUniformCorrectAction :
      ∀ action →
      action ≡ requiredAction upstreamSource →
      action ≡ requiredAction localSource →
      ⊥
    diagnosticSplitsModels :
      DistinguishingExperiment demoSystem upstreamSource localSource
    postObservationCorrectUpstream :
      informationPolicy (observeDemo diagnosticTracer upstreamSource)
      ≡ requiredAction upstreamSource
    postObservationCorrectLocal :
      informationPolicy (observeDemo diagnosticTracer localSource)
      ≡ requiredAction localSource

canonicalPositiveDecisionValueWitness : PositiveDecisionValueWitness
canonicalPositiveDecisionValueWitness =
  positiveDecisionValueWitness
    baselineEquifinality
    uniformActionCannotServeBoth
    diagnosticDistinguishes
    diagnosticPolicyCorrectUpstream
    diagnosticPolicyCorrectLocal

record IdentifiabilityInformationBoundary : Set where
  constructor identifiabilityInformationBoundary
  field
    bestRankedExplanationNeedNotBeIdentified : Bool
    observationalEquivalenceCanBeExperimentRelative : Bool
    activeMeasurementCanSplitAnEquivalenceClass : Bool
    informationValueNeedNotAssumeAProbabilityDistribution : Bool

canonicalIdentifiabilityInformationBoundary :
  IdentifiabilityInformationBoundary
canonicalIdentifiabilityInformationBoundary =
  identifiabilityInformationBoundary true true true true
