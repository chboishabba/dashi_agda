module DASHI.Governance.DependentAuthorityCoercionKernel where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.GuardedPropositionResponseTree as Guarded
import DASHI.Biology.InterventionConsentLongitudinalGovernance as ExistingConsent

data RelationalRole : Set where
  dependentChildRole caregiverRole delegatedSupporterRole educatorRole : RelationalRole
  religiousAuthorityRole institutionalAuthorityRole neutralCustodianRole : RelationalRole

record DevelopmentalState : Set where
  constructor developmentalState
  field
    cognitiveCapacity informationalIndependence regulationCapacity : Nat
    practicalExitCapacity recognisedDecisionAuthority materialDependence : Nat

open DevelopmentalState public

canonicalDependentChildState : DevelopmentalState
canonicalDependentChildState = developmentalState 1 0 1 0 0 10

record ConsentConditions : Set where
  constructor consentConditions
  field
    capacitySufficient informationSufficient voluntary revocable safeRefusalAvailable : Bool

open ConsentConditions public

record ValidConsent (conditions : ConsentConditions) : Set where
  constructor validConsent
  field
    capacityWitness : capacitySufficient conditions ≡ true
    informationWitness : informationSufficient conditions ≡ true
    voluntaryWitness : voluntary conditions ≡ true
    revocabilityWitness : revocable conditions ≡ true
    safeRefusalWitness : safeRefusalAvailable conditions ≡ true

open ValidConsent public

data AssentKind : Set where noAssent developmentalAssent pseudoAssent : AssentKind

data LatentResponse : Set where
  willingResponse uncertainResponse freezeResponse submitResponse fearResponse refusalResponse : LatentResponse

data ObservedBehaviour : Set where observedCompliance observedSilence observedRefusal : ObservedBehaviour

projectBehaviour : LatentResponse → ObservedBehaviour
projectBehaviour willingResponse = observedCompliance
projectBehaviour uncertainResponse = observedSilence
projectBehaviour freezeResponse = observedCompliance
projectBehaviour submitResponse = observedCompliance
projectBehaviour fearResponse = observedCompliance
projectBehaviour refusalResponse = observedRefusal

willingAndSubmissionHaveEqualSurface : projectBehaviour willingResponse ≡ projectBehaviour submitResponse
willingAndSubmissionHaveEqualSurface = refl

willingAndFreezeHaveEqualSurface : projectBehaviour willingResponse ≡ projectBehaviour freezeResponse
willingAndFreezeHaveEqualSurface = refl

willingAndFearHaveEqualSurface : projectBehaviour willingResponse ≡ projectBehaviour fearResponse
willingAndFearHaveEqualSurface = refl

record AuthorityRelation : Set where
  constructor authorityRelation
  field
    authoritySource dependentTarget : RelationalRole
    controlMagnitude dependencyMagnitude exitCapacityMagnitude : Nat
    resistanceCapacityMagnitude sanctionSeverity : Nat
    safeRefusal : Bool

open AuthorityRelation public

data CoerciveMechanism : Set where
  divineSanctionMechanism familialBelongingMechanism institutionalDisciplineMechanism : CoerciveMechanism
  socialExclusionMechanism materialDeprivationMechanism bodilyForceMechanism : CoerciveMechanism

data ThreatOutcomeKind : Set where finiteThreatOutcome indefiniteThreatOutcome eternalThreatOutcome : ThreatOutcomeKind

record ThreatObject : Set where
  constructor threatObject
  field
    threatenedOutcome : String
    outcomeKind : ThreatOutcomeKind
    claimedLikelihood perceivedSeverity : Nat
    threatAuthority : RelationalRole

record CoerciveInteraction : Set where
  constructor coerciveInteraction
  field
    relation : AuthorityRelation
    proposition : Guarded.PropositionNode
    mechanisms : List CoerciveMechanism
    demandPresent : Bool
    demandPresentIsTrue : demandPresent ≡ true
    refusalRestricted : Bool
    refusalRestrictedIsTrue : refusalRestricted ≡ true
    meaningfulPenalty : Bool
    meaningfulPenaltyIsTrue : meaningfulPenalty ≡ true
    observedSurface : ObservedBehaviour
    latentResponseKnown : Bool

open CoerciveInteraction public

record ReligiousCoercion : Set where
  constructor religiousCoercion
  field
    coerciveCore : CoerciveInteraction
    religiouslyFramed : Bool
    religiouslyFramedIsTrue : religiouslyFramed ≡ true

record TransmissionEvent : Set where
  constructor transmissionEvent
  field
    transmitter receiver : RelationalRole
    contentLabel : String
    repeated counterEvidenceRestricted doubtPenalised authorityClosed exitConstrained : Bool

open TransmissionEvent public

record IndoctrinationPattern (event : TransmissionEvent) : Set where
  constructor indoctrinationPattern
  field
    repetitionWitness : repeated event ≡ true
    counterEvidenceRestrictionWitness : counterEvidenceRestricted event ≡ true
    doubtPenaltyWitness : doubtPenalised event ≡ true
    authorityClosureWitness : authorityClosed event ≡ true
    exitConstraintWitness : exitConstrained event ≡ true

record SafeguardingState : Set where
  constructor safeguardingState
  field
    safeDisclosure independentReview dependentWelfarePriority : Bool
    nonConditionalNecessaryCare refusalLegible retaliationBlocked : Bool

open SafeguardingState public

record SafeguardingInvariant (state : SafeguardingState) : Set where
  constructor safeguardingInvariant
  field
    safeDisclosureWitness : safeDisclosure state ≡ true
    independentReviewWitness : independentReview state ≡ true
    dependentWelfarePriorityWitness : dependentWelfarePriority state ≡ true
    nonConditionalCareWitness : nonConditionalNecessaryCare state ≡ true
    refusalLegibleWitness : refusalLegible state ≡ true
    retaliationBlockedWitness : retaliationBlocked state ≡ true

canonicalSafeguardingState : SafeguardingState
canonicalSafeguardingState = safeguardingState true true true true true true

canonicalSafeguardingInvariant : SafeguardingInvariant canonicalSafeguardingState
canonicalSafeguardingInvariant = safeguardingInvariant refl refl refl refl refl refl

existingConsentGovernance : ExistingConsent.InterventionConsentLongitudinalGovernanceRow
existingConsentGovernance = ExistingConsent.longitudinalReviewGovernanceRow

record DependentAuthorityCoercionBoundary : Set where
  constructor dependentAuthorityCoercionBoundary
  field
    religionEqualsHarmPromotion : Bool
    religionEqualsHarmPromotionIsFalse : religionEqualsHarmPromotion ≡ false
    transmissionEqualsCoercionPromotion : Bool
    transmissionEqualsCoercionPromotionIsFalse : transmissionEqualsCoercionPromotion ≡ false
    complianceEqualsConsentPromotion : Bool
    complianceEqualsConsentPromotionIsFalse : complianceEqualsConsentPromotion ≡ false
    silenceEqualsAssentPromotion : Bool
    silenceEqualsAssentPromotionIsFalse : silenceEqualsAssentPromotion ≡ false
    authorityEqualsTruthPromotion : Bool
    authorityEqualsTruthPromotionIsFalse : authorityEqualsTruthPromotion ≡ false
    strongDoctrineEqualsAbusePromotion : Bool
    strongDoctrineEqualsAbusePromotionIsFalse : strongDoctrineEqualsAbusePromotion ≡ false
    distressEqualsMoralFaultPromotion : Bool
    distressEqualsMoralFaultPromotionIsFalse : distressEqualsMoralFaultPromotion ≡ false
    religiousFreedomAbsolutismPromotion : Bool
    religiousFreedomAbsolutismPromotionIsFalse : religiousFreedomAbsolutismPromotion ≡ false
    stateProtectionAbsolutismPromotion : Bool
    stateProtectionAbsolutismPromotionIsFalse : stateProtectionAbsolutismPromotion ≡ false
    boundaryReading : String

open DependentAuthorityCoercionBoundary public

canonicalDependentAuthorityCoercionBoundary : DependentAuthorityCoercionBoundary
canonicalDependentAuthorityCoercionBoundary =
  dependentAuthorityCoercionBoundary
    false refl false refl false refl false refl false refl false refl false refl false refl false refl
    "The generic kernel distinguishes teaching from indoctrination, assent from valid consent, and observed compliance from latent willingness. A child or other dependent subject requires a real counterfactual refusal path; religion, parenting, care, and institutional protection are never promoted to harm or legitimacy merely by label."

canonicalComplianceEqualsConsentPromotionFalse :
  complianceEqualsConsentPromotion canonicalDependentAuthorityCoercionBoundary ≡ false
canonicalComplianceEqualsConsentPromotionFalse =
  complianceEqualsConsentPromotionIsFalse canonicalDependentAuthorityCoercionBoundary
