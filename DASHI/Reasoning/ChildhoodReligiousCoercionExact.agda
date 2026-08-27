module DASHI.Reasoning.ChildhoodReligiousCoercionExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- SOURCE FORMALISATION
--
-- "DASHI Formalisation: Childhood Religious Coercion" (user-supplied working
-- manuscript, 2026).  No external publication author or DOI is asserted.
--
-- This module formalises the manuscript's central typed distinctions:
-- religious transmission is not coercion; compliance is a non-injective
-- projection of latent response; silence is not assent; coercion depends on
-- demand, restricted refusal and penalty; and evidential grade must remain
-- distinct from a proposition's formal derivability.
------------------------------------------------------------------------

data DevelopmentalCapacity : Set where
  dependentChildCapacity : DevelopmentalCapacity
  autonomousAdultCapacity : DevelopmentalCapacity

data ExitCapacity : Set where
  noPracticalExit : ExitCapacity
  practicalExitAvailable : ExitCapacity

data RefusalSafety : Set where
  safeRefusal : RefusalSafety
  penalisedRefusal : RefusalSafety

data ReligiousFraming : Set where
  religiouslyFramed : ReligiousFraming
  nonReligiousFraming : ReligiousFraming

data DemandStatus : Set where
  noDemand : DemandStatus
  complianceDemanded : DemandStatus

data PenaltyStatus : Set where
  noPenalty : PenaltyStatus
  seriousPenalty : PenaltyStatus

data LatentResponse : Set where
  willing : LatentResponse
  uncertain : LatentResponse
  freeze : LatentResponse
  submit : LatentResponse
  fear : LatentResponse
  refuse : LatentResponse

data ObservedBehaviour : Set where
  observedCompliance : ObservedBehaviour
  observedNonCompliance : ObservedBehaviour

behaviourProjection : LatentResponse → ObservedBehaviour
behaviourProjection willing = observedCompliance
behaviourProjection uncertain = observedCompliance
behaviourProjection freeze = observedCompliance
behaviourProjection submit = observedCompliance
behaviourProjection fear = observedCompliance
behaviourProjection refuse = observedNonCompliance

willingAndSubmitProjectToSameBehaviour :
  behaviourProjection willing ≡ behaviourProjection submit
willingAndSubmitProjectToSameBehaviour = refl

willingIsNotSubmit : willing ≡ submit → ⊥
willingIsNotSubmit ()

complianceProjectionIsNonInjective :
  behaviourProjection willing ≡ behaviourProjection submit
  × (willing ≡ submit → ⊥)
complianceProjectionIsNonInjective =
  willingAndSubmitProjectToSameBehaviour , willingIsNotSubmit

data ExpressedResponse : Set where
  expressedYes : ExpressedResponse
  expressedNo : ExpressedResponse
  silence : ExpressedResponse

data AssentStatus : Set where
  meaningfulAssent : AssentStatus
  noAssent : AssentStatus
  pseudoAssent : AssentStatus

assentFrom : RefusalSafety → ExpressedResponse → AssentStatus
assentFrom safeRefusal expressedYes = meaningfulAssent
assentFrom penalisedRefusal expressedYes = pseudoAssent
assentFrom safety expressedNo = noAssent
assentFrom safety silence = noAssent

silenceIsNotAssent :
  (safety : RefusalSafety) →
  assentFrom safety silence ≡ noAssent
silenceIsNotAssent safeRefusal = refl
silenceIsNotAssent penalisedRefusal = refl

penalisedYesIsPseudoAssent :
  assentFrom penalisedRefusal expressedYes ≡ pseudoAssent
penalisedYesIsPseudoAssent = refl

data ConsentStatus : Set where
  validConsent : ConsentStatus
  invalidConsent : ConsentStatus

consentFrom :
  DevelopmentalCapacity →
  ExitCapacity →
  RefusalSafety →
  ExpressedResponse →
  ConsentStatus
consentFrom autonomousAdultCapacity practicalExitAvailable safeRefusal expressedYes =
  validConsent
consentFrom capacity exit safety response = invalidConsent

childComplianceDoesNotConstructValidConsent :
  (exit : ExitCapacity) →
  (safety : RefusalSafety) →
  consentFrom dependentChildCapacity exit safety expressedYes
  ≡ invalidConsent
childComplianceDoesNotConstructValidConsent noPracticalExit safeRefusal = refl
childComplianceDoesNotConstructValidConsent noPracticalExit penalisedRefusal = refl
childComplianceDoesNotConstructValidConsent practicalExitAvailable safeRefusal = refl
childComplianceDoesNotConstructValidConsent practicalExitAvailable penalisedRefusal = refl

data CoercionStatus : Set where
  coercive : CoercionStatus
  nonCoercive : CoercionStatus

coercionFrom :
  DemandStatus →
  RefusalSafety →
  PenaltyStatus →
  CoercionStatus
coercionFrom complianceDemanded penalisedRefusal seriousPenalty = coercive
coercionFrom demand safety penalty = nonCoercive

transmissionWithoutDemandIsNotCoercion :
  (safety : RefusalSafety) →
  (penalty : PenaltyStatus) →
  coercionFrom noDemand safety penalty ≡ nonCoercive
transmissionWithoutDemandIsNotCoercion safeRefusal noPenalty = refl
transmissionWithoutDemandIsNotCoercion safeRefusal seriousPenalty = refl
transmissionWithoutDemandIsNotCoercion penalisedRefusal noPenalty = refl
transmissionWithoutDemandIsNotCoercion penalisedRefusal seriousPenalty = refl

restrictedRefusalAndPenaltyConstructCoercion :
  coercionFrom complianceDemanded penalisedRefusal seriousPenalty
  ≡ coercive
restrictedRefusalAndPenaltyConstructCoercion = refl

data ReligiousCoercionStatus : Set where
  religiousCoercion : ReligiousCoercionStatus
  noReligiousCoercion : ReligiousCoercionStatus

religiousCoercionFrom :
  ReligiousFraming →
  CoercionStatus →
  ReligiousCoercionStatus
religiousCoercionFrom religiouslyFramed coercive = religiousCoercion
religiousCoercionFrom framing status = noReligiousCoercion

religiousContentAloneDoesNotConstructCoercion :
  religiousCoercionFrom religiouslyFramed nonCoercive
  ≡ noReligiousCoercion
religiousContentAloneDoesNotConstructCoercion = refl

data AuthorityClosure : Set where
  corrigibleAuthority : AuthorityClosure
  closedAuthorityLoop : AuthorityClosure

data CorrectionChannel : Set where
  independentCorrection : CorrectionChannel
  noIndependentCorrection : CorrectionChannel

correctionChannel : AuthorityClosure → CorrectionChannel
correctionChannel corrigibleAuthority = independentCorrection
correctionChannel closedAuthorityLoop = noIndependentCorrection

closedAuthorityHasNoIndependentCorrection :
  correctionChannel closedAuthorityLoop ≡ noIndependentCorrection
closedAuthorityHasNoIndependentCorrection = refl

data DisclosureResponse : Set where
  protectAndInvestigate : DisclosureResponse
  ignoreDisclosure : DisclosureResponse
  retaliateAgainstDisclosure : DisclosureResponse

data BetrayalStatus : Set where
  noInstitutionalBetrayal : BetrayalStatus
  institutionalBetrayal : BetrayalStatus

betrayalFrom : DisclosureResponse → BetrayalStatus
betrayalFrom protectAndInvestigate = noInstitutionalBetrayal
betrayalFrom ignoreDisclosure = institutionalBetrayal
betrayalFrom retaliateAgainstDisclosure = institutionalBetrayal

retaliationConstructsInstitutionalBetrayal :
  betrayalFrom retaliateAgainstDisclosure ≡ institutionalBetrayal
retaliationConstructsInstitutionalBetrayal = refl

data EvidenceGrade : Set where
  definitionGrade : EvidenceGrade
  logicalConsequenceGrade : EvidenceGrade
  mechanisticPlausibilityGrade : EvidenceGrade
  crossSectionalAssociationGrade : EvidenceGrade
  longitudinalAssociationGrade : EvidenceGrade
  quasiCausalGrade : EvidenceGrade
  establishedCausalGrade : EvidenceGrade

record GradedClaim : Set₁ where
  constructor gradedClaim
  field
    propositionClass : Set
    evidenceGrade : EvidenceGrade

open GradedClaim public

coercionDefinitionClaim : GradedClaim
coercionDefinitionClaim = gradedClaim CoercionStatus definitionGrade

repeatedCoercionOutcomeClaim : GradedClaim
repeatedCoercionOutcomeClaim =
  gradedClaim ReligiousCoercionStatus mechanisticPlausibilityGrade

record ReligiousCoercionBoundary : Set where
  constructor religiousCoercionBoundary
  field
    complianceIsInjectiveEvidenceOfWillingness : Bool
    complianceIsInjectiveEvidenceOfWillingnessIsFalse :
      complianceIsInjectiveEvidenceOfWillingness ≡ false
    religiousTransmissionIsIntrinsicallyCoercive : Bool
    religiousTransmissionIsIntrinsicallyCoerciveIsFalse :
      religiousTransmissionIsIntrinsicallyCoercive ≡ false
    mechanisticPlausibilityIsEstablishedCausation : Bool
    mechanisticPlausibilityIsEstablishedCausationIsFalse :
      mechanisticPlausibilityIsEstablishedCausation ≡ false

canonicalReligiousCoercionBoundary : ReligiousCoercionBoundary
canonicalReligiousCoercionBoundary =
  religiousCoercionBoundary false refl false refl false refl
