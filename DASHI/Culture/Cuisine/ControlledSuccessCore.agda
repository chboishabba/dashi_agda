module DASHI.Culture.Cuisine.ControlledSuccessCore where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Culture.Cuisine.CuisineKnowledgeSourceAtlas as Sources
import DASHI.Culture.Preservation.ControlledDisclosureCore as Disclosure

------------------------------------------------------------------------
-- Controlled success, designation, carrying capacity, and publicity hazard.
--
-- Recognition can support continuity and livelihoods, but can also create
-- burst demand, worker exposure, ecological pressure, tourism displacement,
-- prestige extraction, or unwanted contact.  This module encodes decision
-- boundaries and leaves empirical assessment to source-specific evidence.
------------------------------------------------------------------------

data DesignationRight : Set where
  rightToProduce : DesignationRight
  rightToUseName : DesignationRight
  rightToDisclose : DesignationRight
  rightToRepresent : DesignationRight
  rightToSublicense : DesignationRight
  rightToAmendSpecification : DesignationRight
  rightToWithdrawPermission : DesignationRight

record CommunityGovernedPracticeDesignation : Set where
  constructor communityGovernedPracticeDesignation
  field
    representedPractice : String
    governingCommunity : String
    territorialRelations : String
    recognisedPractitionerReading : String
    publicSpecification : String
    controlledSpecification : String
    restrictedKnowledgeReading : String
    governedRights : List DesignationRight
    nameUsePolicy : String
    representationPolicy : String
    productionPolicy : String
    tourismPolicy : String
    amendmentProcedure : String
    withdrawalProcedure : String
    communityGovernanceVerified : Bool
    communityGovernanceVerifiedIsFalse :
      communityGovernanceVerified ≡ false

open CommunityGovernedPracticeDesignation public

data CapacityDimension : Set where
  physicalCapacity : CapacityDimension
  ecologicalCapacity : CapacityDimension
  labourCapacity : CapacityDimension
  socialCapacity : CapacityDimension
  ritualCapacity : CapacityDimension
  epistemicCapacity : CapacityDimension

data CapacityStanding : Set where
  withinCapacity : CapacityStanding
  capacityExceeded : CapacityStanding
  capacityUnknown : CapacityStanding

record CarryingCapacityProfile : Set where
  constructor carryingCapacityProfile
  field
    capacityValue : CapacityDimension → Nat
    demandValue : CapacityDimension → Nat
    standing : CapacityDimension → CapacityStanding
    capacityReading : String

open CarryingCapacityProfile public

data OverloadKind : Set where
  demandOverload : OverloadKind
  visibilityExposure : OverloadKind
  marginCollapse : OverloadKind
  tourismOverload : OverloadKind
  ingredientPressure : OverloadKind
  ritualOverload : OverloadKind
  epistemicOverexposure : OverloadKind

data DemandShape : Set where
  smoothDemand : DemandShape
  burstDemand : DemandShape
  viralBatchDemand : DemandShape
  seasonalDemand : DemandShape
  unknownDemandShape : DemandShape

record DemandExposure : Set where
  constructor demandExposure
  field
    objectLabel : String
    baselineAttention : Nat
    amplifiedAttention : Nat
    demandShape : DemandShape
    leadTime : Nat
    sameWindowCapacity : Nat
    perishabilityOrFragility : Nat
    overloadKinds : List OverloadKind
    demandReading : String

open DemandExposure public

canonicalBakeryBatchExposure : DemandExposure
canonicalBakeryBatchExposure =
  demandExposure
    "candidate bakery burst-demand pattern"
    1
    12
    viralBatchDemand
    12
    3
    8
    (demandOverload ∷ visibilityExposure ∷ marginCollapse ∷ [])
    "Long lead times, narrow service windows, perishability, low unit margins, and batch arrivals can make popularity operationally destructive without proving any particular closure cause."

data ContactStanding : Set where
  invitedContact : ContactStanding
  negotiatedContact : ContactStanding
  limitedContact : ContactStanding
  unsolicitedContact : ContactStanding
  refusedContact : ContactStanding
  noContactProtected : ContactStanding

record NoContactProtection : Set where
  constructor noContactProtection
  field
    representedCommunity : String
    contactStanding : ContactStanding
    selfDeterminationReading : String
    territorialBoundary : String
    accessProhibition : String
    publicationProhibition : String
    observationLimit : String
    emergencyOnlyProtocol : String
    externalInterestCreatesPermission : Bool
    externalInterestCreatesPermissionIsFalse :
      externalInterestCreatesPermission ≡ false

open NoContactProtection public

canonicalNoContactBoundary : NoContactProtection
canonicalNoContactBoundary =
  noContactProtection
    "people in voluntary isolation; no community-specific factual claim beyond attributed human-rights guidance"
    noContactProtected
    "no contact is a positive self-determination and protection rule, not missing data"
    "protected territorial boundary"
    "unsolicited entry is prohibited"
    "location and contact-enabling knowledge may be non-disclosable"
    "observation is limited by self-determination, health, and territorial protection"
    "emergency intervention requires a separately governed protocol"
    false
    refl

data ProtectiveFriction : Set where
  apprenticeshipRequired : ProtectiveFriction
  communityIntroductionRequired : ProtectiveFriction
  seasonalAccessOnly : ProtectiveFriction
  nonCommercialUseOnly : ProtectiveFriction
  locationWithheld : ProtectiveFriction
  participantLimit : ProtectiveFriction
  attributionRequired : ProtectiveFriction
  reciprocityRequired : ProtectiveFriction
  noRecording : ProtectiveFriction
  noRedistribution : ProtectiveFriction

data PublicationRisk : Set where
  lowPublicationRisk : PublicationRisk
  controlledPublicationRisk : PublicationRisk
  highPublicationRisk : PublicationRisk
  unknownPublicationRisk : PublicationRisk

data PublicationDecision : Set where
  publishDecision : PublicationDecision
  limitedProjectionDecision : PublicationDecision
  abstainDecision : PublicationDecision

publicationDecision : PublicationRisk → PublicationDecision
publicationDecision lowPublicationRisk = publishDecision
publicationDecision controlledPublicationRisk = limitedProjectionDecision
publicationDecision highPublicationRisk = abstainDecision
publicationDecision unknownPublicationRisk = abstainDecision

highRiskFailsClosed :
  publicationDecision highPublicationRisk ≡ abstainDecision
highRiskFailsClosed = refl

unknownRiskFailsClosed :
  publicationDecision unknownPublicationRisk ≡ abstainDecision
unknownRiskFailsClosed = refl

record PublicationImpactAssessment : Set where
  constructor publicationImpactAssessment
  field
    artifactLabel : String
    representedCommunities : List String
    consentEvidence : List String
    disclosureAuthority : String
    demandProjection : String
    tourismProjection : String
    ingredientPressureProjection : String
    labourPressureProjection : String
    locationRisk : PublicationRisk
    appropriationRisk : PublicationRisk
    harassmentRisk : PublicationRisk
    protectiveFrictions : List ProtectiveFriction
    mitigationPlan : String
    withdrawalMechanism : String
    overallRisk : PublicationRisk
    decision : PublicationDecision
    decisionMatchesRisk : decision ≡ publicationDecision overallRisk

open PublicationImpactAssessment public

canonicalCautiousCuisinePublicationAssessment : PublicationImpactAssessment
canonicalCautiousCuisinePublicationAssessment =
  publicationImpactAssessment
    "candidate situated cuisine public projection"
    ("represented communities remain source-specific" ∷ [])
    []
    "no community disclosure authority supplied"
    "formal legibility may amplify demand and imitation"
    "tourism effect is unresolved"
    "rare ingredient and landrace pressure is unresolved"
    "worker and household labour pressure is unresolved"
    controlledPublicationRisk
    controlledPublicationRisk
    controlledPublicationRisk
    ( attributionRequired
    ∷ locationWithheld
    ∷ nonCommercialUseOnly
    ∷ participantLimit
    ∷ [] )
    "release only an attributed high-level structural projection; retain precise vulnerable details in a governed archive"
    "controlled access can be revoked, but already public copies cannot be guaranteed recoverable"
    controlledPublicationRisk
    limitedProjectionDecision
    refl

record RecognitionInducedDepletion : Set where
  constructor recognitionInducedDepletion
  field
    culturalObject : String
    recognitionEvent : String
    inducedDemand : String
    sustainingConditions : List String
    depletedConditions : List String
    capacityStanding : CapacityStanding
    causalFindingPromoted : Bool
    causalFindingPromotedIsFalse : causalFindingPromoted ≡ false
    depletionReading : String

open RecognitionInducedDepletion public

data RevalorisationState : Set where
  cropLossState : RevalorisationState
  subsistenceFoodState : RevalorisationState
  locallyValuedFoodState : RevalorisationState
  gourmetCommodityState : RevalorisationState
  plannedProductionState : RevalorisationState

record HuitlacocheRevalorisationCase : Set where
  constructor huitlacocheRevalorisationCase
  field
    organismReading : String
    valueStates : List RevalorisationState
    possibleBenefits : List String
    possibleRisks : List String
    producerBenefitVerified : Bool
    producerBenefitVerifiedIsFalse : producerBenefitVerified ≡ false
    communityOutcomeVerified : Bool
    communityOutcomeVerifiedIsFalse : communityOutcomeVerified ≡ false

open HuitlacocheRevalorisationCase public

canonicalHuitlacocheRevalorisationCase : HuitlacocheRevalorisationCase
canonicalHuitlacocheRevalorisationCase =
  huitlacocheRevalorisationCase
    "huitlacoche or cuitlacoche: Ustilago maydis on maize; this is an attributed biological and culinary identification"
    ( cropLossState
    ∷ subsistenceFoodState
    ∷ locallyValuedFoodState
    ∷ gourmetCommodityState
    ∷ plannedProductionState
    ∷ [] )
    ( "possible producer income"
    ∷ "possible support for culinary continuity"
    ∷ "possible market for native maize"
    ∷ "possible reduced waste"
    ∷ [] )
    ( "gourmet capture"
    ∷ "price inflation and reduced local access"
    ∷ "producer invisibility"
    ∷ "agronomic standardisation"
    ∷ "landrace or land pressure"
    ∷ "prestige captured away from growers"
    ∷ [] )
    false
    refl
    false
    refl

data ControlledSuccessNonCollapse : Set where
  nameProtectedDoesNotImplyCommunityProtected : ControlledSuccessNonCollapse
  demandPermittedDoesNotImplyDemandUnlimited : ControlledSuccessNonCollapse
  profitableDoesNotImplyEquitable : ControlledSuccessNonCollapse
  higherMarketValueDoesNotImplyBetterCommunityOutcome : ControlledSuccessNonCollapse
  valuableToVisitDoesNotImplyOpenWithoutLimit : ControlledSuccessNonCollapse
  valuableToLearnDoesNotImplyOpenWithoutLimit : ControlledSuccessNonCollapse
  scientificInterestDoesNotImplyPermissionToContact : ControlledSuccessNonCollapse
  trueDoesNotImplyPublishable : ControlledSuccessNonCollapse
  documentedDoesNotImplyPublic : ControlledSuccessNonCollapse

canonicalControlledSuccessNonCollapses : List ControlledSuccessNonCollapse
canonicalControlledSuccessNonCollapses =
  nameProtectedDoesNotImplyCommunityProtected
  ∷ demandPermittedDoesNotImplyDemandUnlimited
  ∷ profitableDoesNotImplyEquitable
  ∷ higherMarketValueDoesNotImplyBetterCommunityOutcome
  ∷ valuableToVisitDoesNotImplyOpenWithoutLimit
  ∷ valuableToLearnDoesNotImplyOpenWithoutLimit
  ∷ scientificInterestDoesNotImplyPermissionToContact
  ∷ trueDoesNotImplyPublishable
  ∷ documentedDoesNotImplyPublic
  ∷ []

candidateCapacityValue : CapacityDimension → Nat
candidateCapacityValue physicalCapacity = 100
candidateCapacityValue ecologicalCapacity = 60
candidateCapacityValue labourCapacity = 40
candidateCapacityValue socialCapacity = 50
candidateCapacityValue ritualCapacity = 20
candidateCapacityValue epistemicCapacity = 10

candidateDemandValue : CapacityDimension → Nat
candidateDemandValue physicalCapacity = 50
candidateDemandValue ecologicalCapacity = 50
candidateDemandValue labourCapacity = 50
candidateDemandValue socialCapacity = 50
candidateDemandValue ritualCapacity = 50
candidateDemandValue epistemicCapacity = 50

candidateCapacityStanding : CapacityDimension → CapacityStanding
candidateCapacityStanding physicalCapacity = withinCapacity
candidateCapacityStanding ecologicalCapacity = withinCapacity
candidateCapacityStanding labourCapacity = capacityExceeded
candidateCapacityStanding socialCapacity = withinCapacity
candidateCapacityStanding ritualCapacity = capacityExceeded
candidateCapacityStanding epistemicCapacity = capacityExceeded

canonicalCandidateCapacity : CarryingCapacityProfile
canonicalCandidateCapacity =
  carryingCapacityProfile
    candidateCapacityValue
    candidateDemandValue
    candidateCapacityStanding
    "The candidate illustrates weakest-link governance: physical room does not repair labour, ritual, or epistemic over-capacity."

canonicalCandidateDesignation : CommunityGovernedPracticeDesignation
canonicalCandidateDesignation =
  communityGovernedPracticeDesignation
    "situated cultural culinary practice"
    "community governance must be supplied rather than inferred"
    "land, seed, water, migration, and place relations remain explicit"
    "recognised practitioners require a community-specific procedure"
    "high-level public specification"
    "controlled process and lineage specification"
    "restricted or non-exportable knowledge may exist"
    ( rightToProduce
    ∷ rightToUseName
    ∷ rightToDisclose
    ∷ rightToRepresent
    ∷ rightToSublicense
    ∷ rightToAmendSpecification
    ∷ rightToWithdrawPermission
    ∷ [] )
    "name use is distinct from production and disclosure rights"
    "representation is claim-, community-, occasion-, and time-indexed"
    "production conformity does not create spokesperson authority"
    "visitor access remains capacity- and community-governed"
    "amendment requires the designated governance process"
    "withdrawal applies to controlled access; irreversibly public copies remain a residual"
    false
    refl

record ControlledSuccessBoundary : Set₁ where
  constructor controlledSuccessBoundary
  field
    designation : CommunityGovernedPracticeDesignation
    carryingCapacity : CarryingCapacityProfile
    bakeryExposure : DemandExposure
    noContactBoundary : NoContactProtection
    publicationAssessment : PublicationImpactAssessment
    preservationBoundary : Disclosure.PreservationPublicationBoundary
    huitlacocheCase : HuitlacocheRevalorisationCase
    sourceCountReceipt : Sources.canonicalCuisineKnowledgeSourceCount ≡ 22
    nonCollapses : List ControlledSuccessNonCollapse
    controlledSuccessAchievedClaim : Bool
    controlledSuccessAchievedClaimIsFalse :
      controlledSuccessAchievedClaim ≡ false

open ControlledSuccessBoundary public

canonicalControlledSuccessBoundary : ControlledSuccessBoundary
canonicalControlledSuccessBoundary =
  controlledSuccessBoundary
    canonicalCandidateDesignation
    canonicalCandidateCapacity
    canonicalBakeryBatchExposure
    canonicalNoContactBoundary
    canonicalCautiousCuisinePublicationAssessment
    Disclosure.canonicalPreservationPublicationBoundary
    canonicalHuitlacocheRevalorisationCase
    Sources.canonicalCuisineKnowledgeSourceCountIsTwentyTwo
    canonicalControlledSuccessNonCollapses
    false
    refl

canonicalControlledSuccessReceipt : GenericReceipt.GenericReceipt
canonicalControlledSuccessReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "controlled cultural success boundary"
    "DASHI.Culture.Cuisine.ControlledSuccessCore"
    "canonicalControlledSuccessBoundary"
    "formalises designation rights, multidimensional carrying capacity, burst-demand exposure, protective friction, no-contact, publication assessment, recognition depletion, and huitlacoche revalorisation"
    "the boundary does not prove community governance, consent, causal depletion, carrying-capacity measurements, producer benefit, tourism safety, or publication safety"
    "agda -i . DASHI/Culture/Cuisine/ControlledSuccessCore.agda"
