module DASHI.Core.ConsentTemporalExternalityExact where

open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- CONSENT / PERMISSION / AUTHORITY / TEMPORAL EXTERNALITY GEOMETRY
--
-- Source-neutral DASHI mathematics.  Downstream source atlases calibrate FPIC,
-- benefit-sharing, Indigenous governance, climate/intergenerational reasoning,
-- research reuse and other application-specific semantics.  No source is
-- credited with the finite non-factorability theorems below.
------------------------------------------------------------------------

data ActionScope : Set where
  observeOnly collectMaterial initialResearch downstreamReuse publishResult
  commercialise interveneDeploy : ActionScope

data ConsentStatus : Set where
  consentNotSought consentGranted consentWithheld consentWithdrawn : ConsentStatus

data PermissionStatus : Set where
  protocolPermissionAbsent protocolPermissionPresent : PermissionStatus

data AuthorityStatus : Set where
  authorityAbsent authorityPresent : AuthorityStatus

data BenefitSharingStatus : Set where
  benefitSharingAbsent benefitSharingPresent : BenefitSharingStatus

record ScopedConsentState : Set where
  constructor scopedConsentState
  field
    scope : ActionScope
    consent : ConsentStatus
    permission : PermissionStatus
    authority : AuthorityStatus
    benefitSharing : BenefitSharingStatus

open ScopedConsentState public

samePermissionNoConsent : ScopedConsentState
samePermissionNoConsent =
  scopedConsentState initialResearch consentNotSought
    protocolPermissionPresent authorityPresent benefitSharingAbsent

samePermissionWithConsent : ScopedConsentState
samePermissionWithConsent =
  scopedConsentState initialResearch consentGranted
    protocolPermissionPresent authorityPresent benefitSharingAbsent

permissionObserver : ScopedConsentState → PermissionStatus
permissionObserver = permission

consentObserver : ScopedConsentState → ConsentStatus
consentObserver = consent

permissionCannotRecoverConsent :
  INF.FactorsThrough permissionObserver consentObserver → ⊥
permissionCannotRecoverConsent =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      samePermissionNoConsent samePermissionWithConsent refl (λ ()))

sameAuthorityNoConsent : ScopedConsentState
sameAuthorityNoConsent =
  scopedConsentState collectMaterial consentWithheld
    protocolPermissionPresent authorityPresent benefitSharingAbsent

sameAuthorityWithConsent : ScopedConsentState
sameAuthorityWithConsent =
  scopedConsentState collectMaterial consentGranted
    protocolPermissionPresent authorityPresent benefitSharingAbsent

authorityObserver : ScopedConsentState → AuthorityStatus
authorityObserver = authority

authorityCannotRecoverConsent :
  INF.FactorsThrough authorityObserver consentObserver → ⊥
authorityCannotRecoverConsent =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      sameAuthorityNoConsent sameAuthorityWithConsent refl (λ ()))

------------------------------------------------------------------------
-- Consent is scope-indexed.  Initial-study consent does not manufacture
-- downstream-reuse or intervention consent.
------------------------------------------------------------------------

data ConsentFor : ScopedConsentState → ActionScope → Set where
  initialConsent : ConsentFor
    (scopedConsentState initialResearch consentGranted
      protocolPermissionPresent authorityPresent benefitSharingAbsent)
    initialResearch

initialConsentDoesNotAuthorizeReuse :
  ConsentFor
    (scopedConsentState initialResearch consentGranted
      protocolPermissionPresent authorityPresent benefitSharingAbsent)
    downstreamReuse → ⊥
initialConsentDoesNotAuthorizeReuse ()

initialConsentDoesNotAuthorizeIntervention :
  ConsentFor
    (scopedConsentState initialResearch consentGranted
      protocolPermissionPresent authorityPresent benefitSharingAbsent)
    interveneDeploy → ⊥
initialConsentDoesNotAuthorizeIntervention ()

------------------------------------------------------------------------
-- Benefit sharing is separate again: valid consent to a scoped activity does
-- not itself establish a mutually agreed benefit-sharing arrangement.
------------------------------------------------------------------------

consentedNoBenefitSharing : ScopedConsentState
consentedNoBenefitSharing =
  scopedConsentState initialResearch consentGranted
    protocolPermissionPresent authorityPresent benefitSharingAbsent

consentedWithBenefitSharing : ScopedConsentState
consentedWithBenefitSharing =
  scopedConsentState initialResearch consentGranted
    protocolPermissionPresent authorityPresent benefitSharingPresent

consentCannotRecoverBenefitSharing :
  INF.FactorsThrough consentObserver benefitSharing → ⊥
consentCannotRecoverBenefitSharing =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      consentedNoBenefitSharing consentedWithBenefitSharing refl (λ ()))

------------------------------------------------------------------------
-- Temporal distribution: same present benefit can hide different later burden.
------------------------------------------------------------------------

data TemporalTrajectory : Set where
  benefitNowLowLaterBurden benefitNowHighLaterBurden : TemporalTrajectory

data PresentBenefit : Set where samePresentBenefit : PresentBenefit

data LaterBurden : Set where lowerLaterBurden higherLaterBurden : LaterBurden

data PresentVoice : Set where samePresentVoice : PresentVoice

data FutureRepresentation : Set where
  futureInterestRepresented futureInterestUnrepresented : FutureRepresentation

presentBenefit : TemporalTrajectory → PresentBenefit
presentBenefit _ = samePresentBenefit

laterBurden : TemporalTrajectory → LaterBurden
laterBurden benefitNowLowLaterBurden = lowerLaterBurden
laterBurden benefitNowHighLaterBurden = higherLaterBurden

presentVoice : TemporalTrajectory → PresentVoice
presentVoice _ = samePresentVoice

futureRepresentation : TemporalTrajectory → FutureRepresentation
futureRepresentation benefitNowLowLaterBurden = futureInterestRepresented
futureRepresentation benefitNowHighLaterBurden = futureInterestUnrepresented

presentBenefitCannotRecoverLaterBurden :
  INF.FactorsThrough presentBenefit laterBurden → ⊥
presentBenefitCannotRecoverLaterBurden =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      benefitNowLowLaterBurden benefitNowHighLaterBurden refl (λ ()))

presentVoiceCannotRecoverFutureRepresentation :
  INF.FactorsThrough presentVoice futureRepresentation → ⊥
presentVoiceCannotRecoverFutureRepresentation =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      benefitNowLowLaterBurden benefitNowHighLaterBurden refl (λ ()))

------------------------------------------------------------------------
-- Future generations are represented by stewardship/representation obligations,
-- not fictional retroactive consent from persons who cannot presently consent.
------------------------------------------------------------------------

data TemporalStanding : Set where
  presentlyAffected futureAffected : TemporalStanding

data ConsentEvidence : TemporalStanding → Set where
  presentPartyConsentEvidence : ConsentEvidence presentlyAffected

data IntergenerationalRepresentation : TemporalStanding → Set where
  futureStewardshipRepresentation : IntergenerationalRepresentation futureAffected

futureAffectedHasNoPresentConsentEvidence : ConsentEvidence futureAffected → ⊥
futureAffectedHasNoPresentConsentEvidence ()

futureRepresentationIsNotFutureConsent :
  IntergenerationalRepresentation futureAffected → ConsentEvidence futureAffected → ⊥
futureRepresentationIsNotFutureConsent _ = futureAffectedHasNoPresentConsentEvidence

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ConsentTemporalExternalityBoundary : Set where
  constructor consent-temporal-externality-boundary
  field
    permissionEqualsConsent : Bool
    permissionEqualsConsentIsFalse : permissionEqualsConsent ≡ false
    authorityEqualsConsent : Bool
    authorityEqualsConsentIsFalse : authorityEqualsConsent ≡ false
    initialConsentAutomaticallyCoversDownstreamReuse : Bool
    initialConsentAutomaticallyCoversDownstreamReuseIsFalse :
      initialConsentAutomaticallyCoversDownstreamReuse ≡ false
    consentAutomaticallyEstablishesBenefitSharing : Bool
    consentAutomaticallyEstablishesBenefitSharingIsFalse :
      consentAutomaticallyEstablishesBenefitSharing ≡ false
    presentBenefitDeterminesFutureBurden : Bool
    presentBenefitDeterminesFutureBurdenIsFalse :
      presentBenefitDeterminesFutureBurden ≡ false
    presentVoiceDeterminesFutureRepresentation : Bool
    presentVoiceDeterminesFutureRepresentationIsFalse :
      presentVoiceDeterminesFutureRepresentation ≡ false
    representationOfFutureInterestsEqualsFutureConsent : Bool
    representationOfFutureInterestsEqualsFutureConsentIsFalse :
      representationOfFutureInterestsEqualsFutureConsent ≡ false

canonicalConsentTemporalExternalityBoundary : ConsentTemporalExternalityBoundary
canonicalConsentTemporalExternalityBoundary =
  consent-temporal-externality-boundary
    false refl false refl false refl false refl false refl false refl false refl
