module DASHI.Cognition.CausalRegimeMeasureFrame where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Axis-indexed causal validation.
------------------------------------------------------------------------

data ValidationStatus : Set where
  satisfied : ValidationStatus
  violated : ValidationStatus
  undetermined : ValidationStatus
  inapplicable : ValidationStatus

data CausalAxis : Set where
  associationAxis : CausalAxis
  temporalAxis : CausalAxis
  mechanismAxis : CausalAxis
  confounderAxis : CausalAxis
  counterfactualAxis : CausalAxis

record AxisValidation : Set where
  constructor axisValidation
  field
    axis : CausalAxis
    status : ValidationStatus
    evidenceTag : String

open AxisValidation public

record CausalCertificate : Set where
  field
    temporalValidation : AxisValidation
    mechanismValidation : AxisValidation
    confounderValidation : AxisValidation
    counterfactualValidation : AxisValidation

    temporalClosed : status temporalValidation ≡ satisfied
    mechanismClosed : status mechanismValidation ≡ satisfied
    confounderClosed : status confounderValidation ≡ satisfied
    counterfactualClosed : status counterfactualValidation ≡ satisfied

open CausalCertificate public

------------------------------------------------------------------------
-- Evaluation frames: causal closure, regime transport, and probability role
-- are distinct coordinates.
------------------------------------------------------------------------

data ProbabilityFrame : Set where
  realWorldP : ProbabilityFrame
  riskNeutralQ : ProbabilityFrame
  purposeIndexedProbability : ProbabilityFrame

data StatementRole : Set where
  descriptiveRole : StatementRole
  causalRole : StatementRole
  policyRole : StatementRole
  pricingRole : StatementRole
  forecastingRole : StatementRole
  riskControlRole : StatementRole

data ClosureAxis : Set where
  associationalClosure : ClosureAxis
  causalClosure : ClosureAxis
  interventionalClosure : ClosureAxis
  measureRoleClosure : ClosureAxis

record EvaluationFrame : Set where
  constructor evaluationFrame
  field
    evidenceContext : String
    regime : String
    probabilityFrame : ProbabilityFrame
    statementRole : StatementRole
    interventionBoundary : String

open EvaluationFrame public

record TransportCertificate
    (source target : EvaluationFrame) : Set₁ where
  field
    assumptionPreservation : Set
    causalMechanismPreservation : Set
    regimeInvariance : Set
    measureCompatibility : Set
    statementRoleCompatibility : Set

open TransportCertificate public

record ClosureProfile : Set where
  constructor closureProfile
  field
    associationStatus : ValidationStatus
    causalStatus : ValidationStatus
    interventionStatus : ValidationStatus
    measureRoleStatus : ValidationStatus

open ClosureProfile public

record PromotionWitness
    (role : StatementRole)
    (profile : ClosureProfile) : Set where
  field
    requiredAxes : List ClosureAxis
    requiredAxesAreClosed : Set

open PromotionWitness public

pricingFrame : EvaluationFrame
pricingFrame =
  evaluationFrame
    "market surface and no-arbitrage assumptions"
    "pricing regime"
    riskNeutralQ
    pricingRole
    "pricing operation only"

forecastFrame : EvaluationFrame
forecastFrame =
  evaluationFrame
    "historical and current real-world evidence"
    "deployment-sensitive market regime"
    realWorldP
    forecastingRole
    "strategy deployment changes the process"

record ProbabilityRoleBoundary : Set where
  constructor probabilityRoleBoundary
  field
    pricingAndForecastingSeparated : Bool
    qPricingImpliesPForecasting : Bool
    qPricingImpliesPForecastingIsFalse : qPricingImpliesPForecasting ≡ false

canonicalProbabilityRoleBoundary : ProbabilityRoleBoundary
canonicalProbabilityRoleBoundary =
  probabilityRoleBoundary true false refl

------------------------------------------------------------------------
-- A deployment-ready signal needs more than historical association.
------------------------------------------------------------------------

record ReflexiveSignalCertificate : Set₁ where
  field
    historicalEdge : Set
    causalMechanism : Set
    agentResponseModel : Set
    deploymentInvariance : Set
    crowdingRobustness : Set
    narrativeRegimeRobustness : Set

open ReflexiveSignalCertificate public

record FrameTransportBoundary : Set where
  constructor frameTransportBoundary
  field
    observationalClosureImpliesInterventionClosure : Bool
    implicationBlocked :
      observationalClosureImpliesInterventionClosure ≡ false
    probabilityRoleTransportAutomatic : Bool
    probabilityRoleTransportAutomaticIsFalse :
      probabilityRoleTransportAutomatic ≡ false

canonicalFrameTransportBoundary : FrameTransportBoundary
canonicalFrameTransportBoundary =
  frameTransportBoundary false refl false refl
