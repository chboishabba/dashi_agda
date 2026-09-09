module DASHI.Cognition.PNF.SensibLawBrightonS185DirectionalApplicabilityRegressionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Algebra.Trit as Trit
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawDirectionalEvidenceApplicabilityBridgeExact as Directional
import DASHI.Cognition.PNF.SensibLawApplicabilityPrerequisiteMeetExact as Meet
import DASHI.Cognition.PNF.SensibLawViolationPrerequisiteMeetExact as ViolationMeet
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal
import DASHI.Interop.SensibLawNatSourceSupportAcquisitionExact as Source
import DASHI.Interop.SensibLawNatSourcePropositionVerificationExact as Verify
import DASHI.Interop.SensibLawBrightonForm11SourceSpanVerificationExact as Form11Source
import DASHI.Law.SensibLawHousingEpisodeEvidenceLineageExact as Housing

------------------------------------------------------------------------
-- BRIGHTON / RTRA s 185 SINGLE-EPISODE REGRESSION
--
-- This is deliberately narrower than the longitudinal housing sequence.
-- It uses the 24 January 2023 Brighton Form 11 carrier only as a source-backed
-- assertion/remedy context and tests the full existing chain through
-- applicability and then the existing violation meet.
--
-- External source roles are preserved:
--   * Queensland legislation owns the legal duty in RTRA Act 2008 s 185;
--   * Queensland RTA owns the prescribed Form 11 / s 325 procedure;
--   * the matter Form 11 owns the episode-specific assertions it contains.
-- DASHI owns only the typed reconstruction/weld below.
--
-- Historical authority at the exact matter date is an explicit receipt.  This
-- module does not infer a 24 January 2023 in-force proposition from a nearby or
-- current compilation merely because the wording appears stable.
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

rtraSection185Source : HousingLegalSourceAttribution
rtraSection185Source =
  housingLegalSourceAttribution
    primaryLegislation
    "Queensland Residential Tenancies and Rooming Accommodation Act 2008"
    "official Queensland legislation, s 185; exact 24 January 2023 temporal applicability requires separate historical-authority receipt"
    "continuing-tenancy lessor maintenance / fit-to-live-in / good-repair duty"
    "Queensland legislation s 185 source attribution for Brighton consumer"

rtaForm11GuidanceSource : HousingLegalSourceAttribution
rtaForm11GuidanceSource =
  housingLegalSourceAttribution
    administrativeFormGuidance
    "Queensland Residential Tenancies Authority — Notice to remedy breach (Form 11)"
    "official RTA Form 11 / RTRA s 325 procedural source"
    "Form 11 records a claimed/alleged breach and a demand to remedy; issuing the form does not itself determine that the breach occurred"
    "Queensland RTA Form 11 source attribution"

brightonForm11SourceResidualReference : String
brightonForm11SourceResidualReference =
  Source.residualReference Form11Source.form11Residual

brightonForm11SourceArtifactReceiptReference : String
brightonForm11SourceArtifactReceiptReference =
  Form11Source.form11ArtifactReceiptReference

brightonForm11TargetClaimDigest : String
brightonForm11TargetClaimDigest = Form11Source.form11TargetClaimDigest

canonicalForm11SourceSupportPaid :
  Verify.sourceSupportPaid Form11Source.form11Admission ≡ true
canonicalForm11SourceSupportPaid = Form11Source.form11SourceSupportPaid

canonicalForm11SourceSupportPositive :
  Verify.supportTrit Form11Source.form11Admission ≡ Trit.pos
canonicalForm11SourceSupportPositive = Form11Source.form11SupportTritPositive

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
    matterCarrierReferenceIsForm11 :
      sourceIdentity matterCarrier ≡ "RTA Form 11.pdf"
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

    -- Exact source artifact -> exact proposition -> +1 support payment.
    sourceResidualIsBrightonForm11MatterSupport :
      Source.residualReference residual ≡ brightonForm11SourceResidualReference
    sourceVerificationTargetsExactMatterProposition :
      Verify.targetClaimDigest demand ≡ propositionReference matter
    sourceVerificationTargetMatchesPaidForm11Claim :
      Verify.targetClaimDigest demand ≡ brightonForm11TargetClaimDigest
    sourceVerificationUsesExactForm11ArtifactReceipt :
      Verify.sourceArtifactReceiptReference demand
      ≡ brightonForm11SourceArtifactReceiptReference
    sourceVerificationDispositionIsSupported :
      Verify.disposition receipt ≡ Verify.supported
    sourceAdmissionIsCanonical :
      admission ≡ Verify.admitSourceSupport receipt
    sourceSpanPaymentReference : String

    sourceConditionedApplicability :
      Directional.SourceConditionedApplicabilityMeetInput
        receipt admission state

    sameMatterPropositionAsDirectionalTarget : Set
    sameForm11CarrierAsResolvedLegalEvidence : Set

    section185AuthoritySource : HousingLegalSourceAttribution
    section185AuthorityIsPrimaryLegislation :
      sourceRole section185AuthoritySource ≡ primaryLegislation
    sameSection185AuthorityAsApplicabilityMeet : Set
    historicalSection185AuthorityAt24Jan2023 : Set
    section185AuthorityWeldReference : String

    form11GuidanceSource : HousingLegalSourceAttribution
    form11GuidanceIsAdministrative :
      sourceRole form11GuidanceSource ≡ administrativeFormGuidance
    form11ProcedureMatchesMatterForm : Set

    queenslandJurisdictionReceipt : Set
    temporalScopeIncludes24Jan2023Receipt : Set
    sameS185IssueUsedByApplicabilityMeet : Set

    violationInput : ViolationMeet.ViolationMeetInput state
    violationUsesExactCompiledApplicability :
      ViolationMeet.receipt
        (ViolationMeet.applicability
          (ViolationMeet.prerequisites violationInput))
      ≡ Directional.compileSourceConditionedApplicability
          sourceConditionedApplicability
    violationDecisionIsCaseSpecific : Set

    noMedicalCausationPromotion : Set
    noCrossEpisodeCommonCausePromotion : Set
    regressionReference : String
open BrightonS185RegressionInput public

brightonCanonicalAdmissionPaysPositive :
  ∀ {residual demand receipt admission state}
    (input : BrightonS185RegressionInput
      {residual} {demand} receipt admission state) →
  Verify.sourceSupportPaid admission ≡ true
brightonCanonicalAdmissionPaysPositive input
  rewrite sourceAdmissionIsCanonical input
        | sourceVerificationDispositionIsSupported input = refl

brightonCanonicalAdmissionHasPositiveTrit :
  ∀ {residual demand receipt admission state}
    (input : BrightonS185RegressionInput
      {residual} {demand} receipt admission state) →
  Verify.supportTrit admission ≡ Trit.pos
brightonCanonicalAdmissionHasPositiveTrit input
  rewrite sourceAdmissionIsCanonical input
        | sourceVerificationDispositionIsSupported input = refl

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

compileBrightonS185Violation :
  ∀ {residual demand receipt admission state} →
  BrightonS185RegressionInput
    {residual} {demand} receipt admission state →
  Legal.ViolationReceipt
compileBrightonS185Violation input =
  ViolationMeet.compileViolationMeet (violationInput input)

brightonViolationConsumesExactCompiledApplicability :
  ∀ {residual demand receipt admission state}
    (input : BrightonS185RegressionInput
      {residual} {demand} receipt admission state) →
  ViolationMeet.receipt
    (ViolationMeet.applicability
      (ViolationMeet.prerequisites (violationInput input)))
  ≡ compileBrightonS185Applicability input
brightonViolationConsumesExactCompiledApplicability input =
  violationUsesExactCompiledApplicability input

------------------------------------------------------------------------
-- FIREWALLS
------------------------------------------------------------------------

data Form11AssertionAutomaticallyEstablishesBreach : Set where
data PositiveSourceSupportAutomaticallyEstablishesS185Violation : Set where
data Section185AuthorityAutomaticallyEstablishesMatterFacts : Set where
data NearbyCompilationAutomaticallyEstablishesHistoricalAuthority : Set where
data UnweldedSection185LabelAuthorizesApplicability : Set where
data HealthContextAutomaticallyEstablishesMedicalCausation : Set where
data OneHousingEpisodeAutomaticallyEstablishesSystemicWrongdoing : Set where
data ApplicabilityAutomaticallyEstablishesViolation : Set where
data ViolationAutomaticallyEstablishesLiability : Set where

form11AssertionDoesNotEstablishBreach :
  Form11AssertionAutomaticallyEstablishesBreach → ⊥
form11AssertionDoesNotEstablishBreach ()

positiveSupportDoesNotEstablishS185Violation :
  PositiveSourceSupportAutomaticallyEstablishesS185Violation → ⊥
positiveSupportDoesNotEstablishS185Violation ()

section185AuthorityDoesNotEstablishMatterFacts :
  Section185AuthorityAutomaticallyEstablishesMatterFacts → ⊥
section185AuthorityDoesNotEstablishMatterFacts ()

nearbyCompilationDoesNotEstablishHistoricalAuthority :
  NearbyCompilationAutomaticallyEstablishesHistoricalAuthority → ⊥
nearbyCompilationDoesNotEstablishHistoricalAuthority ()

unweldedSection185LabelDoesNotAuthorizeApplicability :
  UnweldedSection185LabelAuthorizesApplicability → ⊥
unweldedSection185LabelDoesNotAuthorizeApplicability ()

healthContextDoesNotEstablishMedicalCausation :
  HealthContextAutomaticallyEstablishesMedicalCausation → ⊥
healthContextDoesNotEstablishMedicalCausation ()

oneEpisodeDoesNotEstablishSystemicWrongdoing :
  OneHousingEpisodeAutomaticallyEstablishesSystemicWrongdoing → ⊥
oneEpisodeDoesNotEstablishSystemicWrongdoing ()

applicabilityDoesNotEstablishViolation :
  ApplicabilityAutomaticallyEstablishesViolation → ⊥
applicabilityDoesNotEstablishViolation ()

violationDoesNotEstablishLiability :
  ViolationAutomaticallyEstablishesLiability → ⊥
violationDoesNotEstablishLiability ()

record BrightonS185RegressionBoundary : Set where
  constructor brighton-s185-regression-boundary
  field
    oneEpisodeOnly : Bool
    form11IsMatterEvidenceCarrier : Bool
    exactSourceResidualRequired : Bool
    exactTargetClaimBindingRequired : Bool
    exactSourceArtifactReceiptRequired : Bool
    supportedDispositionRequired : Bool
    canonicalSourceAdmissionRequired : Bool
    positiveSupportPaidByCanonicalAdmission : Bool
    positiveTritPaidByCanonicalAdmission : Bool
    exactPrivateSourceSpanReceiptAvailable : Bool
    section185IsIndependentLegalAuthority : Bool
    positiveSourceSupportRequiredBeforeBridge : Bool
    sameMatterPropositionWeldRequired : Bool
    sameEvidenceCarrierWeldRequired : Bool
    sameSection185AuthorityWeldRequired : Bool
    exactHistoricalAuthorityReceiptRequired : Bool
    exactJurisdictionReceiptRequired : Bool
    exactTemporalScopeReceiptRequired : Bool
    existingApplicabilityCompilerRetained : Bool
    existingViolationCompilerRetained : Bool
    exactApplicabilityReceiptReusedByViolation : Bool
    form11AssertionCreatesBreach : Bool
    positiveSupportCreatesViolation : Bool
    legalAuthorityCreatesMatterFact : Bool
    nearbyCompilationCreatesHistoricalAuthority : Bool
    unweldedSection185LabelAuthorizesApplicability : Bool
    healthContextCreatesMedicalCausation : Bool
    oneEpisodeCreatesSystemicWrongdoing : Bool
    applicabilityCreatesViolation : Bool
    violationCreatesLiability : Bool

canonicalBrightonS185RegressionBoundary : BrightonS185RegressionBoundary
canonicalBrightonS185RegressionBoundary =
  brighton-s185-regression-boundary
    true true true true true true true true true true true true true true true true true true true true true
    false false false false false false false false false
