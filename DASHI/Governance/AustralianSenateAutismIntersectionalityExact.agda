module DASHI.Governance.AustralianSenateAutismIntersectionalityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.IntersectionalLongitudinalResidualDynamics as Longitudinal
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.SituatedFibreDynamicsEverything as Situated
import DASHI.Governance.AustralianSenateAutismInquiryExact as Inquiry
import DASHI.Governance.RecognitionDistributionRepresentationAxesExact as Fraser
import DASHI.Governance.SituatedConstituency as Constituency

------------------------------------------------------------------------
-- AUSTRALIAN SENATE AUTISM INQUIRY -> EXISTING INTERSECTIONAL MACHINERY
--
-- This is a bridge, not a new intersectionality ontology. Recommendation 18
-- supplies a source-bound requirement to attend to multiple situated cohorts.
-- Existing DASHI owners supply non-factorability, longitudinal fibres,
-- situated constituency, and recognition/distribution/representation.
--
-- The finite list named by the committee is not promoted to an exhaustive
-- ontology of autistic people. Place, history, relation and institution remain
-- first-class coordinates, and affected constituencies may articulate further
-- axes not anticipated by the report or this bridge.
------------------------------------------------------------------------

recommendation18SourceFact : Inquiry.AttributedAutismInquiryFact
recommendation18SourceFact = Inquiry.recommendation18Fact

------------------------------------------------------------------------
-- Existing longitudinal axis bundle selected for this consumer.
-- Regional/remoteness is carried by place as well as constituency axes;
-- complex support need is not treated as an identity axis.
------------------------------------------------------------------------

autismIntersectionalAxes : List Longitudinal.IntersectionalAxis
autismIntersectionalAxes =
  Longitudinal.neurotypeAxis
  ∷ Longitudinal.disabilityAxis
  ∷ Longitudinal.classAxis
  ∷ Longitudinal.genderAxis
  ∷ Longitudinal.sexualityAxis
  ∷ Longitudinal.raceAxis
  ∷ Longitudinal.colonialityAxis
  ∷ Longitudinal.lawAxis
  ∷ Longitudinal.institutionAxis
  ∷ []

autismGovernanceAxes : List Constituency.GovernanceAxis
autismGovernanceAxes =
  Constituency.neurotypeAxis
  ∷ Constituency.disabilityAxis
  ∷ Constituency.classAxis
  ∷ Constituency.genderAxis
  ∷ Constituency.sexualityAxis
  ∷ Constituency.ethnicityAxis
  ∷ Constituency.colonialityAxis
  ∷ Constituency.regionAxis
  ∷ Constituency.ruralUrbanAxis
  ∷ Constituency.institutionalAccessAxis
  ∷ Constituency.namedGovernanceAxis "First Nations self-identification / community authority"
  ∷ Constituency.namedGovernanceAxis "culturally and linguistically diverse context"
  ∷ []

canonicalAutismSituatedConstituency : Constituency.SituatedConstituency
canonicalAutismSituatedConstituency =
  Constituency.mkSituatedConstituency
    "autistic people addressed by Recommendation 18"
    "Australia, with regional/remote and local place retained"
    2022
    "Senate inquiry / Commonwealth policy and service institutions"
    autismGovernanceAxes
    "affected autistic constituencies retain direct articulation of needs and axes; committee enumeration is non-exhaustive"

------------------------------------------------------------------------
-- Native fibre-over-time carrier. SituatedFibreDynamicsEverything is imported
-- as the repo rollup; this application supplies only autism-policy semantics.
------------------------------------------------------------------------

autismIntersectionalLongitudinalCarrier :
  Longitudinal.IntersectionalResidualCarrier
autismIntersectionalLongitudinalCarrier =
  Longitudinal.mkIntersectionalResidualCarrierOf
    "autistic person / autistic constituency"
    2025
    "situated Australian place"
    "family, peer, community and service relations"
    "health, education, employment, housing, justice and social-service institutions"
    autismIntersectionalAxes
    "National Autism Strategy implementation must be read through situated time/place/relation/institution/axis fibres rather than an autism-only scalar."

autismIntersectionalLongitudinalCarrierExists : Bool
autismIntersectionalLongitudinalCarrierExists = true

------------------------------------------------------------------------
-- Existing non-factorability result from the inquiry owner remains the basic
-- proof that an autism-only observer is insufficient.
------------------------------------------------------------------------

autismOnlyCannotRecoverSituatedNeed :
  NF.FactorsThrough Inquiry.autismOnlyObserver Inquiry.situatedSupportNeed → ⊥
autismOnlyCannotRecoverSituatedNeed = Inquiry.autismLabelCannotRecoverSituatedNeed

------------------------------------------------------------------------
-- Existing Fraser axis separation is reused directly. Recognition of autistic
-- identity or inclusion language cannot by itself pay material distribution;
-- similarly, formal representation/co-design does not by itself establish
-- access to services, resources or outcomes.
------------------------------------------------------------------------

recognitionCannotRecoverDistribution :
  NF.FactorsThrough Fraser.recognition Fraser.distribution → ⊥
recognitionCannotRecoverDistribution = Fraser.recognitionCannotRecoverDistribution

recognitionAlonePaysDistribution : Bool
recognitionAlonePaysDistribution = false

representationAlonePaysDistribution : Bool
representationAlonePaysDistribution = false

------------------------------------------------------------------------
-- Strategy intersectionality weld.
--
-- The 2025 Strategy/First Action Plan explicitly defines intersectionality in
-- terms of overlapping discrimination/marginalisation and describes evidence
-- as including culturally responsive, LGBTQIA+-inclusive and lived-experience
-- components. This is a downstream same-object thematic weld to Recommendation
-- 18, not yet a payment of each cohort-specific implementation obligation.
------------------------------------------------------------------------

data IntersectionalityWeldStatus : Set where
  senateRecommendationPaid : IntersectionalityWeldStatus
  strategyTextSameThemePaid : IntersectionalityWeldStatus
  cohortSpecificActionPaymentOpen : IntersectionalityWeldStatus
  cohortSpecificOutcomePaymentOpen : IntersectionalityWeldStatus

record Recommendation18StrategyWeld : Set where
  constructor recommendation18-strategy-weld
  field
    senateFact : Inquiry.AttributedAutismInquiryFact
    strategySource : Source.AttributedSource
    status : IntersectionalityWeldStatus
    statement : String
    recommendationEqualsImplementation : Bool
    recommendationEqualsImplementationIsFalse : recommendationEqualsImplementation ≡ false
    strategyTextEqualsImplementation : Bool
    strategyTextEqualsImplementationIsFalse : strategyTextEqualsImplementation ≡ false
    strategyTextEqualsOutcome : Bool
    strategyTextEqualsOutcomeIsFalse : strategyTextEqualsOutcome ≡ false

open Recommendation18StrategyWeld public

canonicalRecommendation18StrategyWeld : Recommendation18StrategyWeld
canonicalRecommendation18StrategyWeld =
  recommendation18-strategy-weld
    Inquiry.recommendation18Fact
    Inquiry.nationalAutismStrategy2025
    strategyTextSameThemePaid
    "The final Strategy/First Action Plan carries explicit intersectionality language and overlapping-disadvantage semantics consonant with Recommendation 18; literal cohort-specific action and outcome discharge remain separate payments."
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Non-exhaustiveness and affected-constituency authority boundary.
------------------------------------------------------------------------

committeeCohortListExhaustive : Bool
committeeCohortListExhaustive = false

singleAxisAutomaticallyAdequate : Bool
singleAxisAutomaticallyAdequate = false

strategyIntersectionalityTextPaysImplementation : Bool
strategyIntersectionalityTextPaysImplementation = false

affectedConstituencyMayArticulateFurtherAxes : Bool
affectedConstituencyMayArticulateFurtherAxes =
  Constituency.AxisAwareRepresentationBoundary.affectedConstituencyMayArticulateAxes
    Constituency.canonicalAxisAwareRepresentationBoundary

------------------------------------------------------------------------
-- Explicit WrongType firewalls.
------------------------------------------------------------------------

data FiniteCohortListEqualsExhaustiveIntersectionality : Set where
data RecognitionEqualsMaterialAccess : Set where
data CoDesignPresenceEqualsRepresentativeAdequacy : Set where
data StrategyIntersectionalityTextEqualsCohortOutcome : Set where
data ComplexNeedEqualsIdentityAxis : Set where

finiteCohortListDoesNotEqualExhaustiveIntersectionality :
  FiniteCohortListEqualsExhaustiveIntersectionality → ⊥
finiteCohortListDoesNotEqualExhaustiveIntersectionality ()

recognitionDoesNotEqualMaterialAccess :
  RecognitionEqualsMaterialAccess → ⊥
recognitionDoesNotEqualMaterialAccess ()

coDesignPresenceDoesNotEqualRepresentativeAdequacy :
  CoDesignPresenceEqualsRepresentativeAdequacy → ⊥
coDesignPresenceDoesNotEqualRepresentativeAdequacy ()

strategyIntersectionalityTextDoesNotEqualCohortOutcome :
  StrategyIntersectionalityTextEqualsCohortOutcome → ⊥
strategyIntersectionalityTextDoesNotEqualCohortOutcome ()

complexNeedDoesNotEqualIdentityAxis : ComplexNeedEqualsIdentityAxis → ⊥
complexNeedDoesNotEqualIdentityAxis ()

------------------------------------------------------------------------
-- Pareto refinement. After the semantic intersectionality weld, the next
-- paying leaf is not more demographic enumeration; it is cohort-specific
-- action evidence joined to place/institution/representation/distribution.
------------------------------------------------------------------------

data IntersectionalPaymentLeaf : Set where
  recommendation18SemanticLeaf : IntersectionalPaymentLeaf
  strategyIntersectionalitySemanticLeaf : IntersectionalPaymentLeaf
  cohortActionLeaf : IntersectionalPaymentLeaf
  cohortAccessDistributionLeaf : IntersectionalPaymentLeaf
  cohortRepresentationLeaf : IntersectionalPaymentLeaf
  longitudinalOutcomeLeaf : IntersectionalPaymentLeaf

intersectionalPaymentFrontier : IntersectionalPaymentLeaf
intersectionalPaymentFrontier = cohortActionLeaf

highestAlphaIntersectionalResidual : String
highestAlphaIntersectionalResidual =
  "Acquire action-level evidence for named/affected cohorts and join it with material access/distribution, direct representation, place/institution context and longitudinal outcomes; do not spend effort merely adding more labels."

record AutismIntersectionalityBoundary : Set where
  constructor autism-intersectionality-boundary
  field
    reusesExistingNonFactorability : Bool
    reusesExistingLongitudinalCarrier : Bool
    reusesExistingSituatedConstituency : Bool
    reusesExistingParticipationAxes : Bool
    committeeEnumerationIsExhaustive : Bool
    strategyTextAutomaticallyPaysAction : Bool
    representationAutomaticallyPaysDistribution : Bool

canonicalAutismIntersectionalityBoundary : AutismIntersectionalityBoundary
canonicalAutismIntersectionalityBoundary =
  autism-intersectionality-boundary
    true true true true false false false
