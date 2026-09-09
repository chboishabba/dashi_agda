module DASHI.Cognition.PNF.SensibLawBrightonS185DirectionalApplicabilityRegressionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawDirectionalEvidenceApplicabilityBridgeExact as Directional
import DASHI.Cognition.PNF.SensibLawApplicabilityPrerequisiteMeetExact as Meet
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal
import DASHI.Interop.SensibLawNatSourceSupportAcquisitionExact as Source
import DASHI.Interop.SensibLawNatSourcePropositionVerificationExact as Verify
import DASHI.Law.SensibLawHousingEpisodeEvidenceLineageExact as Housing

------------------------------------------------------------------------
-- BRIGHTON / RTRA s 185 SINGLE-EPISODE REGRESSION
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
    "official Queensland legislation, in-force version dated 19 January 2023, s 185(3)"
    "while the tenancy continues, the lessor must maintain the premises so they remain fit for the tenant to live in and maintain the premises/inclusions in good repair"
    "Queensland legislation historical s 185 source attribution for 24 January 2023 Brighton consumer"

rtaForm11GuidanceSource : HousingLegalSourceAttribution
rtaForm11GuidanceSource =
  housingLegalSourceAttribution
    administrativeFormGuidance
    "Queensland Residential Tenancies Authority — Notice to remedy breach (Form 11)"
    "official RTA Form 11 guidance; administrative function only"
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

    sameMatterPropositionAsDirectionalTarget : Set
    sameForm11CarrierAsResolvedLegalEvidence : Set

    section185AuthoritySource : HousingLegalSourceAttribution
    section185AuthorityIsPrimaryLegislation :
      sourceRole section185AuthoritySource ≡ primaryLegislation
    sameSection185AuthorityAsApplicabilityMeet : Set
    section185AuthorityWeldReference : String

    form11GuidanceSource : HousingLegalSourceAttribution
    form11GuidanceIsAdministrative :
      sourceRole form11GuidanceSource ≡ administrativeFormGuidance

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
      (Meet.semanticInput
        (Directional.applicabilityInput
          (sourceConditionedApplicability input)))
brightonApplicabilityStillUsesExistingLegalGate input = refl

------------------------------------------------------------------------
-- FIREWALLS
------------------------------------------------------------------------

data Form11AssertionAutomaticallyEstablishesBreach : Set where
data PositiveSourceSupportAutomaticallyEstablishesS185Violation : Set where
data Section185AuthorityAutomaticallyEstablishesMatterFacts : Set where
data UnweldedSection185LabelAuthorizesApplicability : Set where
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

unweldedSection185LabelDoesNotAuthorizeApplicability :
  UnweldedSection185LabelAuthorizesApplicability → ⊥
unweldedSection185LabelDoesNotAuthorizeApplicability ()

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
    sameSection185AuthorityWeldRequired : Bool
    existingApplicabilityCompilerRetained : Bool
    form11AssertionCreatesBreach : Bool
    positiveSupportCreatesViolation : Bool
    legalAuthorityCreatesMatterFact : Bool
    unweldedSection185LabelAuthorizesApplicability : Bool
    healthContextCreatesMedicalCausation : Bool
    oneEpisodeCreatesSystemicWrongdoing : Bool
    applicabilityCreatesLiability : Bool

canonicalBrightonS185RegressionBoundary : BrightonS185RegressionBoundary
canonicalBrightonS185RegressionBoundary =
  brighton-s185-regression-boundary
    true true true true true true true true
    false false false false false false false
