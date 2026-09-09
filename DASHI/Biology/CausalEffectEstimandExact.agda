module DASHI.Biology.CausalEffectEstimandExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.MultiscaleCausalProvenanceProofSearchRouterExact as Router
import DASHI.Biology.CausalIdentificationFamiliesExact as Identification

------------------------------------------------------------------------
-- CAUSAL EFFECT ESTIMANDS
--
-- Identification and estimand are separate coordinates.  An identification
-- family says why a causal contrast may be admissible; an estimand says exactly
-- which causal contrast is targeted: for which units/population, intervention,
-- comparator, outcome and time horizon.  This owner is intentionally agnostic
-- about numeric probability/expectation machinery; applications supply the
-- aggregation and contrast semantics rather than inheriting an invented mean.
------------------------------------------------------------------------

data CausalEstimandKind : Set where
  averagePopulationEffect : CausalEstimandKind
  averageTreatedEffect : CausalEstimandKind
  individualOrLineageEffect : CausalEstimandKind
  controlledDirectEffect : CausalEstimandKind
  mediatedIndirectEffect : CausalEstimandKind
  trajectoryEffect : CausalEstimandKind
  neuralBehaviouralInterventionEffect : CausalEstimandKind

record CausalEstimandScope : Set₁ where
  constructor causal-estimand-scope
  field
    Unit Population Intervention Comparator Outcome Time : Set
    inPopulation : Unit → Population → Set
    interventionOutcome : Unit → Intervention → Time → Outcome
    comparatorOutcome : Unit → Comparator → Time → Outcome
    population : Population
    intervention : Intervention
    comparator : Comparator
    horizon : Time
    populationReference : String
    interventionReference : String
    comparatorReference : String
    outcomeReference : String
    timeHorizonReference : String

open CausalEstimandScope public

record EffectAlgebra (scope : CausalEstimandScope) : Set₁ where
  constructor effect-algebra
  field
    EffectValue : Set
    unitContrast : Unit scope → Outcome scope → Outcome scope → EffectValue
    PopulationAggregate : Set
    aggregatePopulation :
      Population scope →
      (Unit scope → EffectValue) →
      PopulationAggregate
    aggregationReference : String
    contrastReference : String

open EffectAlgebra public

unitEffectAtHorizon :
  (scope : CausalEstimandScope) →
  (algebra : EffectAlgebra scope) →
  Unit scope → EffectValue algebra
unitEffectAtHorizon scope algebra unit =
  unitContrast algebra unit
    (interventionOutcome scope unit (intervention scope) (horizon scope))
    (comparatorOutcome scope unit (comparator scope) (horizon scope))

record AveragePopulationEffectEstimand
    (scope : CausalEstimandScope)
    (algebra : EffectAlgebra scope) : Set₁ where
  constructor average-population-effect-estimand
  field
    aggregate : PopulationAggregate algebra
    aggregateIsTargetPopulationContrast :
      aggregate
      ≡ aggregatePopulation algebra
          (population scope)
          (unitEffectAtHorizon scope algebra)
    estimandReference : String

open AveragePopulationEffectEstimand public

record AverageTreatedEffectEstimand
    (scope : CausalEstimandScope)
    (algebra : EffectAlgebra scope) : Set₁ where
  constructor average-treated-effect-estimand
  field
    Treated : Unit scope → Set
    TreatedPopulation : Set
    treatedPopulation : TreatedPopulation
    aggregateTreated :
      TreatedPopulation →
      (Unit scope → EffectValue algebra) →
      PopulationAggregate algebra
    aggregate : PopulationAggregate algebra
    aggregateIsTreatedContrast :
      aggregate
      ≡ aggregateTreated
          treatedPopulation
          (unitEffectAtHorizon scope algebra)
    treatedDefinitionReference : String
    estimandReference : String

open AverageTreatedEffectEstimand public

record IndividualLineageEffectEstimand
    (scope : CausalEstimandScope)
    (algebra : EffectAlgebra scope) : Set₁ where
  constructor individual-lineage-effect-estimand
  field
    selectedUnit : Unit scope
    selectedUnitInPopulation : inPopulation scope selectedUnit (population scope)
    effect : EffectValue algebra
    effectIsSelectedUnitContrast :
      effect ≡ unitEffectAtHorizon scope algebra selectedUnit
    lineageOrSubjectReference : String
    estimandReference : String

open IndividualLineageEffectEstimand public

record MediationEstimandSurface
    (scope : CausalEstimandScope) : Set₁ where
  constructor mediation-estimand-surface
  field
    Mediator : Set
    mediatorUnderIntervention : Unit scope → Intervention scope → Time scope → Mediator
    mediatorUnderComparator : Unit scope → Comparator scope → Time scope → Mediator
    DirectEffect : Set
    IndirectEffect : Set
    directEffectReceipt : DirectEffect
    indirectEffectReceipt : IndirectEffect
    mediatorReference : String
    directEffectReference : String
    indirectEffectReference : String

open MediationEstimandSurface public

record TrajectoryEffectEstimand
    (scope : CausalEstimandScope) : Set₁ where
  constructor trajectory-effect-estimand
  field
    TrajectoryEffect : Set
    interventionTrajectory : Unit scope → Time scope → Outcome scope
    comparatorTrajectory : Unit scope → Time scope → Outcome scope
    trajectoryEffectReceipt : TrajectoryEffect
    pathReference : String
    estimandReference : String

open TrajectoryEffectEstimand public

record NeuralBehaviouralEffectEstimand
    (scope : CausalEstimandScope) : Set₁ where
  constructor neural-behavioural-effect-estimand
  field
    NeuralReadout BehaviourReadout CognitiveReadout : Set
    neuralReadout : Unit scope → Intervention scope → Time scope → NeuralReadout
    behaviourReadout : Unit scope → Intervention scope → Time scope → BehaviourReadout
    cognitiveReadout : Unit scope → Intervention scope → Time scope → CognitiveReadout
    Effect : Set
    effectReceipt : Effect
    neuralReference : String
    behaviourReference : String
    cognitiveReference : String
    estimandReference : String

open NeuralBehaviouralEffectEstimand public

data EstimandKindWitness
    (scope : CausalEstimandScope)
    (algebra : EffectAlgebra scope) :
    CausalEstimandKind → Set₁ where
  averagePopulationWitness :
    AveragePopulationEffectEstimand scope algebra →
    EstimandKindWitness scope algebra averagePopulationEffect
  averageTreatedWitness :
    AverageTreatedEffectEstimand scope algebra →
    EstimandKindWitness scope algebra averageTreatedEffect
  individualLineageWitness :
    IndividualLineageEffectEstimand scope algebra →
    EstimandKindWitness scope algebra individualOrLineageEffect
  controlledDirectWitness :
    MediationEstimandSurface scope →
    EstimandKindWitness scope algebra controlledDirectEffect
  mediatedIndirectWitness :
    MediationEstimandSurface scope →
    EstimandKindWitness scope algebra mediatedIndirectEffect
  trajectoryWitness :
    TrajectoryEffectEstimand scope →
    EstimandKindWitness scope algebra trajectoryEffect
  neuralBehaviouralWitness :
    NeuralBehaviouralEffectEstimand scope →
    EstimandKindWitness scope algebra neuralBehaviouralInterventionEffect

EstimandEffectProposition :
  ∀ {scope algebra kind} →
  EstimandKindWitness scope algebra kind → Set
EstimandEffectProposition {scope} {algebra}
  (averagePopulationWitness estimand) =
  aggregate estimand
  ≡ aggregatePopulation algebra
      (population scope)
      (unitEffectAtHorizon scope algebra)
EstimandEffectProposition {scope} {algebra}
  (averageTreatedWitness estimand) =
  aggregate estimand
  ≡ aggregateTreated estimand
      (treatedPopulation estimand)
      (unitEffectAtHorizon scope algebra)
EstimandEffectProposition {scope} {algebra}
  (individualLineageWitness estimand) =
  effect estimand
  ≡ unitEffectAtHorizon scope algebra (selectedUnit estimand)
EstimandEffectProposition (controlledDirectWitness mediation) =
  DirectEffect mediation
EstimandEffectProposition (mediatedIndirectWitness mediation) =
  IndirectEffect mediation
EstimandEffectProposition (trajectoryWitness estimand) =
  TrajectoryEffect estimand
EstimandEffectProposition (neuralBehaviouralWitness estimand) =
  Effect estimand

estimandEffectReceipt :
  ∀ {scope algebra kind}
    (witness : EstimandKindWitness scope algebra kind) →
  EstimandEffectProposition witness
estimandEffectReceipt (averagePopulationWitness estimand) =
  aggregateIsTargetPopulationContrast estimand
estimandEffectReceipt (averageTreatedWitness estimand) =
  aggregateIsTreatedContrast estimand
estimandEffectReceipt (individualLineageWitness estimand) =
  effectIsSelectedUnitContrast estimand
estimandEffectReceipt (controlledDirectWitness mediation) =
  directEffectReceipt mediation
estimandEffectReceipt (mediatedIndirectWitness mediation) =
  indirectEffectReceipt mediation
estimandEffectReceipt (trajectoryWitness estimand) =
  trajectoryEffectReceipt estimand
estimandEffectReceipt (neuralBehaviouralWitness estimand) =
  NeuralBehaviouralEffectEstimand.effectReceipt estimand

record CausalEffectEstimand : Set₂ where
  constructor causal-effect-estimand
  field
    scope : CausalEstimandScope
    algebra : EffectAlgebra scope
    kind : CausalEstimandKind
    kindWitness : EstimandKindWitness scope algebra kind
    estimandReference : String
    scopeReference : String

open CausalEffectEstimand public

EffectProposition : CausalEffectEstimand → Set
EffectProposition estimand = EstimandEffectProposition (kindWitness estimand)

effectReceipt :
  (estimand : CausalEffectEstimand) → EffectProposition estimand
effectReceipt estimand = estimandEffectReceipt (kindWitness estimand)

record CausalAttributionEstimandBinding
    {Value : Set}
    {claim : Router.CrossLevelCausalClaim Value}
    {causalDesign : Router.CrossLevelCausalDesign claim}
    (attribution : Router.CrossLevelCausalAttribution claim causalDesign)
    (installation : Identification.CrossLevelIdentificationInstallation causalDesign)
    (estimand : CausalEffectEstimand) : Set₂ where
  constructor causal-attribution-estimand-binding
  field
    effectTypeMatchesEstimand :
      Router.CausalEffect attribution claim ≡ EffectProposition estimand
    attributedEffectIsEstimandEffect :
      subst (λ Effect → Effect)
        effectTypeMatchesEstimand
        (Router.effectWitness attribution)
      ≡ effectReceipt estimand
    consumerReference : String
    bindingReference : String

open CausalAttributionEstimandBinding public

data IdentificationMeansEstimandKnownPermission : Set where
data PopulationEffectMeansIndividualEffectPermission : Set where
data IndividualEffectMeansPopulationEffectPermission : Set where
data ATTMeansATEPermission : Set where
data EndpointEffectMeansTrajectoryEffectPermission : Set where
data DirectEffectMeansIndirectEffectPermission : Set where
data NeuralEffectMeansThoughtIdentityPermission : Set where
data InternalEffectMeansUniversalTransportPermission : Set where
data CausalEffectWithoutPopulationTimeInterventionPermission : Set where
data EstimandTagWithoutMatchingWitnessPermission : Set where

identificationDoesNotDetermineEstimand :
  IdentificationMeansEstimandKnownPermission → ⊥
identificationDoesNotDetermineEstimand ()
populationEffectDoesNotDetermineIndividualEffect :
  PopulationEffectMeansIndividualEffectPermission → ⊥
populationEffectDoesNotDetermineIndividualEffect ()
individualEffectDoesNotDeterminePopulationEffect :
  IndividualEffectMeansPopulationEffectPermission → ⊥
individualEffectDoesNotDeterminePopulationEffect ()
attDoesNotDefinitionallyEqualAte : ATTMeansATEPermission → ⊥
attDoesNotDefinitionallyEqualAte ()
endpointEffectDoesNotDetermineTrajectoryEffect :
  EndpointEffectMeansTrajectoryEffectPermission → ⊥
endpointEffectDoesNotDetermineTrajectoryEffect ()
directEffectDoesNotDetermineIndirectEffect :
  DirectEffectMeansIndirectEffectPermission → ⊥
directEffectDoesNotDetermineIndirectEffect ()
neuralEffectDoesNotIdentifyThought : NeuralEffectMeansThoughtIdentityPermission → ⊥
neuralEffectDoesNotIdentifyThought ()
internalEffectDoesNotAutomaticallyTransport :
  InternalEffectMeansUniversalTransportPermission → ⊥
internalEffectDoesNotAutomaticallyTransport ()
causalEffectCannotFloatFreeOfScope :
  CausalEffectWithoutPopulationTimeInterventionPermission → ⊥
causalEffectCannotFloatFreeOfScope ()
estimandKindCannotFloatFreeOfMatchingWitness :
  EstimandTagWithoutMatchingWitnessPermission → ⊥
estimandKindCannotFloatFreeOfMatchingWitness ()

record CausalEffectEstimandBoundary : Set where
  constructor causal-effect-estimand-boundary
  field
    identificationAndEstimandAreSeparate : Bool
    populationInterventionComparatorOutcomeTimeAreExplicit : Bool
    estimandKindRequiresMatchingWitness : Bool
    ateAndAttRemainDistinct : Bool
    populationAndIndividualEffectsRemainDistinct : Bool
    endpointAndTrajectoryEffectsRemainDistinct : Bool
    directAndIndirectEffectsRemainDistinct : Bool
    neuralEffectAndThoughtIdentityRemainDistinct : Bool
    effectEstimateAutomaticallyTransports : Bool
    probabilityOrExpectationAlgebraInventedHere : Bool

canonicalCausalEffectEstimandBoundary : CausalEffectEstimandBoundary
canonicalCausalEffectEstimandBoundary =
  causal-effect-estimand-boundary
    true true true true true true true true false false
