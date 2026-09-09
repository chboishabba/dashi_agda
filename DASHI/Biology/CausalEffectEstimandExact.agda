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

------------------------------------------------------------------------
-- Common estimand scope.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Domain-supplied contrast and aggregation semantics.
------------------------------------------------------------------------

record EffectAlgebra (scope : CausalEstimandScope) : Set₁ where
  constructor effect-algebra
  field
    EffectValue : Set

    unitContrast :
      Unit scope → Outcome scope → Outcome scope → EffectValue

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
    (interventionOutcome scope unit
      (intervention scope) (horizon scope))
    (comparatorOutcome scope unit
      (comparator scope) (horizon scope))

------------------------------------------------------------------------
-- Population-average effect.  The owner names the population and aggregation
-- but does not identify PopulationAggregate with a real-valued expectation.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Effect among treated/exposed units.  Treated membership is explicit; ATT is
-- not definitionally the same object as a population-average effect.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Individual / lineage-specific effect.
------------------------------------------------------------------------

record IndividualLineageEffectEstimand
    (scope : CausalEstimandScope)
    (algebra : EffectAlgebra scope) : Set₁ where
  constructor individual-lineage-effect-estimand
  field
    selectedUnit : Unit scope
    selectedUnitInPopulation :
      inPopulation scope selectedUnit (population scope)

    effect : EffectValue algebra
    effectIsSelectedUnitContrast :
      effect ≡ unitEffectAtHorizon scope algebra selectedUnit

    lineageOrSubjectReference : String
    estimandReference : String

open IndividualLineageEffectEstimand public

------------------------------------------------------------------------
-- Mediation estimands.
--
-- Direct and indirect effects require an explicit mediator carrier and separate
-- domain-supplied effect propositions.  No additive decomposition is assumed.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Trajectory effect.
--
-- Endpoint effects and path-sensitive effects are different consumers.  A path
-- effect therefore carries the whole time-indexed outcome surface plus an
-- application-supplied trajectory contrast.
------------------------------------------------------------------------

record TrajectoryEffectEstimand
    (scope : CausalEstimandScope) : Set₁ where
  constructor trajectory-effect-estimand
  field
    TrajectoryEffect : Set

    interventionTrajectory :
      Unit scope → Time scope → Outcome scope
    comparatorTrajectory :
      Unit scope → Time scope → Outcome scope

    trajectoryEffectReceipt : TrajectoryEffect

    pathReference : String
    estimandReference : String

open TrajectoryEffectEstimand public

------------------------------------------------------------------------
-- Neural/behavioural intervention effect.
--
-- The neural intervention, neural readout, effector/behavioural readout and
-- cognitive outcome remain separate coordinates.  This is an estimand surface,
-- not a neural-state == thought identity theorem.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Generic selected estimand.
------------------------------------------------------------------------

record CausalEffectEstimand : Set₂ where
  constructor causal-effect-estimand
  field
    scope : CausalEstimandScope
    algebra : EffectAlgebra scope
    kind : CausalEstimandKind

    EffectProposition : Set
    effectReceipt : EffectProposition

    estimandReference : String
    scopeReference : String

open CausalEffectEstimand public

------------------------------------------------------------------------
-- Bind an estimand to the already-identified cross-level causal attribution.
-- The attribution's effect proposition for this exact claim must be definitionally
-- transported to the selected estimand proposition.  Identification family and
-- estimand therefore remain orthogonal but same-claim welded.
------------------------------------------------------------------------

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
      Router.CausalEffect attribution claim
      ≡ EffectProposition estimand

    attributedEffectIsEstimandEffect :
      subst (λ Effect → Effect)
        effectTypeMatchesEstimand
        (Router.effectWitness attribution)
      ≡ effectReceipt estimand

    consumerReference : String
    bindingReference : String

open CausalAttributionEstimandBinding public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data IdentificationMeansEstimandKnownPermission : Set where

data PopulationEffectMeansIndividualEffectPermission : Set where

data IndividualEffectMeansPopulationEffectPermission : Set where

data ATTMeansATEPermission : Set where

data EndpointEffectMeansTrajectoryEffectPermission : Set where

data DirectEffectMeansIndirectEffectPermission : Set where

data NeuralEffectMeansThoughtIdentityPermission : Set where

data InternalEffectMeansUniversalTransportPermission : Set where

data CausalEffectWithoutPopulationTimeInterventionPermission : Set where

identificationDoesNotDetermineEstimand :
  IdentificationMeansEstimandKnownPermission → ⊥
identificationDoesNotDetermineEstimand ()

populationEffectDoesNotDetermineIndividualEffect :
  PopulationEffectMeansIndividualEffectPermission → ⊥
populationEffectDoesNotDetermineIndividualEffect ()

individualEffectDoesNotDeterminePopulationEffect :
  IndividualEffectMeansPopulationEffectPermission → ⊥
individualEffectDoesNotDeterminePopulationEffect ()

attDoesNotDefinitionallyEqualAte :
  ATTMeansATEPermission → ⊥
attDoesNotDefinitionallyEqualAte ()

endpointEffectDoesNotDetermineTrajectoryEffect :
  EndpointEffectMeansTrajectoryEffectPermission → ⊥
endpointEffectDoesNotDetermineTrajectoryEffect ()

directEffectDoesNotDetermineIndirectEffect :
  DirectEffectMeansIndirectEffectPermission → ⊥
directEffectDoesNotDetermineIndirectEffect ()

neuralEffectDoesNotIdentifyThought :
  NeuralEffectMeansThoughtIdentityPermission → ⊥
neuralEffectDoesNotIdentifyThought ()

internalEffectDoesNotAutomaticallyTransport :
  InternalEffectMeansUniversalTransportPermission → ⊥
internalEffectDoesNotAutomaticallyTransport ()

causalEffectCannotFloatFreeOfScope :
  CausalEffectWithoutPopulationTimeInterventionPermission → ⊥
causalEffectCannotFloatFreeOfScope ()

record CausalEffectEstimandBoundary : Set where
  constructor causal-effect-estimand-boundary
  field
    identificationAndEstimandAreSeparate : Bool
    populationInterventionComparatorOutcomeTimeAreExplicit : Bool
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
    true true true true true true true false false
