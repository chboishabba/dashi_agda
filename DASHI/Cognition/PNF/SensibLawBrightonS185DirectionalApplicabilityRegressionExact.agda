module DASHI.Cognition.PNF.SensibLawBrightonS185DirectionalApplicabilityRegressionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Algebra.Trit as Trit
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawDirectionalEvidenceApplicabilityBridgeExact as Directional
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal
import DASHI.Interop.SensibLawNatSourceSupportAcquisitionExact as Source
import DASHI.Interop.SensibLawNatSourcePropositionVerificationExact as Verify
import DASHI.Law.SensibLawHousingEpisodeEvidenceLineageExact as Housing

------------------------------------------------------------------------
-- BRIGHTON / RTRA s 185 SINGLE-EPISODE REGRESSION
--
-- This is deliberately narrower than the longitudinal housing sequence.
-- It uses the 24 January 2023 Brighton Form 11 carrier only as a source-backed
-- assertion/remedy context and tests that positive proposition support still
-- has to pass through the existing legal applicability meet.
--
-- External source roles are preserved:
--   * Queensland legislation owns the legal duty in RTRA Act 2008 s 185;
--   * Queensland RTA owns the administrative description of Form 11;
--   * the matter Form 11 owns the episode-specific assertions it contains.
-- DASHI owns only the typed reconstruction/weld below.
------------------------------------------------------------------------

data HousingLegalSourceRole : Set where
  primaryLegislation : HousingLegalSourceRole
  administrativeFormGuidance : HousingLegalSourceRole
  matterEvidenceCarrier : HousingLegalSourceRole

record HousingLegalSourceAttribution : Set where
  constructor housingLegalSourceAttribution
  field
    sourceRole : HousingLegalSourceRole
    sourceIdentity : String
    sourcePin : String
    propositionBoundary : String
    attributionReference : String
open HousingLegalSourceAttribution public

rtra2023Section185Source : HousingLegalSourceAttribution
rtra2023Section185Source =
  housingLegalSourceAttribution
    primaryLegislation
    "Queensland Residential Tenancies and Rooming Accommodation Act 2008"
    "official Queensland legislation, version current 1 July 2023, s 185(3)"
    "while the tenancy continues, the lessor must maintain the premises so they remain fit for the tenant to live in and maintain the premises/inclusions in good repair"
    "Queensland legislation s 185 source attribution"

rtaForm11GuidanceSource : HousingLegalSourceAttribution
rtaForm11GuidanceSource =
  housingLegalSourceAttribution
    administrativeFormGuidance
    "Queensland Residential Tenancies Authority — Notice to remedy breach (Form 11)"
    "official RTA Form 11 guidance"
    "Form 11 records a claimed/alleged breach and a demand to remedy; issuing the form does not itself determine that the breach occurred"
    "Queensland RTA Form 11 source attribution"

record BrightonS185MatterProposition : Set₁ where
  constructor brightonS185MatterProposition
  field
    form11Receipt : Set
    exitReportReceipt : Set
    episode : Housing.HousingEpisode
    episodeIsExactBrightonEpisode :
      episode ≡ Housing.brightonEpisode form11Receipt exitReportReceipt
    matterCarrier : HousingLegalSourceAttribution
    matterCarrierRoleIsEvidence :
      sourceRole matterCarrier ≡ matterEvidenceCarrier
    assertedConditionReference : String
    assertedConditionReceipt : Set
    propositionReference : String
open BrightonS185MatterProposition public

record BrightonS185RegressionInput
    {residual : Source.NatSourceSupportResidual}
    {demand : Verify.SourceVerificationDemand residual}
    (receipt : Verify.SourceVerificationReceipt demand)
    (admission : Verify.SourceSupportAdmission receipt)
    (state : Status.SemanticCommitmentState) : Set₁ where
  constructor brightonS185RegressionInput
  field
    matter : BrightonS185MatterProposition
    sourceConditionedApplicability :
      Directional.SourceConditionedApplicabilityMeetInput
        receipt admission state

    -- The matter assertion must be the same proposition/evidence object used
    -- by the directional bridge; string similarity is insufficient.
    sameMatterPropositionAsDirectionalTarget : Set
    sameForm11CarrierAsResolvedLegalEvidence : Set

    -- The legal source remains independently supplied to the existing meet.
    section185AuthoritySource : HousingLegalSourceAttribution
    section185AuthorityIsPrimaryLegislation :
      sourceRole section185AuthoritySource ≡ primaryLegislation
    form11GuidanceSource : HousingLegalSourceAttribution
    form11GuidanceIsAdministrative :
      sourceRole form11GuidanceSource ≡ administrativeFormGuidance

    -- This regression is intentionally applicability-scoped.  It creates no
    -- medical-causation, violation, liability, remedy or systemic-pattern
    -- payment by construction.
    noMedicalCausationPromotion : Set
    noCrossEpisodeCommonCausePromotion : Set
    regressionReference : String
open BrightonS185RegressionInput public

compileBrightonS185Applicability :
  ∀ {residual demand receipt admission state} →
  BrightonS185RegressionInput
    {residual} {demand} receipt admission state →
  Legal.WrongTypeApplicabilityReceipt
compileBrightonS185Applicability input =
  Directional.compileSourceConditionedApplicability
    (sourceConditionedApplicability input)

brightonApplicabilityStillUsesExistingLegalGate :
  ∀ {residual demand receipt admission state}
    (input : BrightonS185RegressionInput
      {residual} {demand} receipt admission state) →
  Legal.resultingApplicability (compileBrightonS185Applicability input)
  ≡ Legal.SemanticLegalInputGate.resultingApplicability
      (DASHI.Cognition.PNF.SensibLawApplicabilityPrerequisiteMeetExact.semanticInput
        (DASHI.Cognition.PNF.SensibLawDirectionalEvidenceApplicabilityBridgeExact.applicabilityInput
          (sourceConditionedApplicability input)))
brightonApplicabilityStillUsesExistingLegalGate input = refl

------------------------------------------------------------------------
-- FIREWALLS
------------------------------------------------------------------------

data Form11AssertionAutomaticallyEstablishesBreach : Set where
data PositiveSourceSupportAutomaticallyEstablishesS185Violation : Set where
data Section185AuthorityAutomaticallyEstablishesMatterFacts : Set where
data HealthContextAutomaticallyEstablishesMedicalCausation : Set where
data OneHousingEpisodeAutomaticallyEstablishesSystemicWrongdoing : Set where
data ApplicabilityAutomaticallyEstablishesLiability : Set where

form11AssertionDoesNotEstablishBreach :
  Form11AssertionAutomaticallyEstablishesBreach → ⊥
form11AssertionDoesNotEstablishBreach ()

positiveSupportDoesNotEstablishS185Violation :
  PositiveSourceSupportAutomaticallyEstablishesS185Violation → ⊥
positiveSupportDoesNotEstablishS185Violation ()

section185AuthorityDoesNotEstablishMatterFacts :
  Section185AuthorityAutomaticallyEstablishesMatterFacts → ⊥
section185AuthorityDoesNotEstablishMatterFacts ()

healthContextDoesNotEstablishMedicalCausation :
  HealthContextAutomaticallyEstablishesMedicalCausation → ⊥
healthContextDoesNotEstablishMedicalCausation ()

oneEpisodeDoesNotEstablishSystemicWrongdoing :
  OneHousingEpisodeAutomaticallyEstablishesSystemicWrongdoing → ⊥
oneEpisodeDoesNotEstablishSystemicWrongdoing ()

applicabilityDoesNotEstablishLiability :
  ApplicabilityAutomaticallyEstablishesLiability → ⊥
applicabilityDoesNotEstablishLiability ()

record BrightonS185RegressionBoundary : Set where
  constructor brighton-s185-regression-boundary
  field
    oneEpisodeOnly : Bool
    form11IsMatterEvidenceCarrier : Bool
    section185IsIndependentLegalAuthority : Bool
    positiveSourceSupportRequiredBeforeBridge : Bool
    sameMatterPropositionWeldRequired : Bool
    sameEvidenceCarrierWeldRequired : Bool
    existingApplicabilityCompilerRetained : Bool
    form11AssertionCreatesBreach : Bool
    positiveSupportCreatesViolation : Bool
    legalAuthorityCreatesMatterFact : Bool
    healthContextCreatesMedicalCausation : Bool
    oneEpisodeCreatesSystemicWrongdoing : Bool
    applicabilityCreatesLiability : Bool

canonicalBrightonS185RegressionBoundary : BrightonS185RegressionBoundary
canonicalBrightonS185RegressionBoundary =
  brighton-s185-regression-boundary
    true true true true true true true
    false false false false false false
