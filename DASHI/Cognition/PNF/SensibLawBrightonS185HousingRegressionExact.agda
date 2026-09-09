module DASHI.Cognition.PNF.SensibLawBrightonS185HousingRegressionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawDirectionalEvidenceApplicabilityBridgeExact as Directional
import DASHI.Cognition.PNF.SensibLawViolationPrerequisiteMeetExact as ViolationMeet
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Interop.SensibLawNatSourceSupportAcquisitionExact as Source
import DASHI.Interop.SensibLawNatSourcePropositionVerificationExact as Verify
import DASHI.Law.SensibLawHousingEpisodeEvidenceLineageExact as Housing

------------------------------------------------------------------------
-- ONE REAL HOUSING LEGAL-TEST REGRESSION: BRIGHTON / RTRA s 185
--
-- This is deliberately one episode and one legal issue.  It does not consume
-- the Herries -> Brighton -> Chapel Hill longitudinal pattern as proof of any
-- systemic proposition.
--
-- Test-definition source:
--   Residential Tenancies and Rooming Accommodation Act 2008 (Qld), s 185.
--   The legal proposition used here is the continuing-tenancy maintenance
--   duty: premises must remain fit to live in and premises/inclusions must be
--   maintained in good repair.
--
-- Procedural source:
--   RTA Notice to remedy breach (Form 11), made under s 325.
--
-- Case factual carrier:
--   the 24 January 2023 Brighton Form 11 already pinned by the merged #845
--   HousingEpisode fixture.  It is a party-generated case source that asserts
--   unresolved mould / roof-repair conditions and health context.  Its claim
--   that a breach existed is NOT itself the legal test-definition source and
--   does not adjudicate violation.
------------------------------------------------------------------------

rtraActSourceReference : String
rtraActSourceReference =
  "Queensland Parliamentary Counsel: Residential Tenancies and Rooming Accommodation Act 2008 (Qld)"

s185SourceReference : String
s185SourceReference =
  "RTRA 2008 (Qld) s 185(3)(a)-(b): continuing lessor maintenance / good-repair duties"

form11ProceduralSourceReference : String
form11ProceduralSourceReference =
  "Residential Tenancies Authority: Notice to remedy breach (Form 11), RTRA s 325"

brightonForm11CarrierReference : String
brightonForm11CarrierReference = "RTA Form 11.pdf"

brightonEpisodeReference : String
brightonEpisodeReference = "17 Gordon Street Brighton tenancy displacement episode"

brightonPremisesReference : String
brightonPremisesReference = "17 Gordon Street, Brighton QLD 4017"

brightonTargetFactReference : String
brightonTargetFactReference =
  "24 January 2023 Brighton Form 11 asserts unresolved mould / roof-repair conditions during the tenancy"

brightonS185IssueReference : String
brightonS185IssueReference =
  "whether the source-supported unresolved-condition proposition fits the RTRA s 185 continuing maintenance duty"

------------------------------------------------------------------------
-- SOURCE ATTRIBUTION SPLIT
------------------------------------------------------------------------

data HousingRegressionSourceRole : Set where
  legalTestDefinitionSource : HousingRegressionSourceRole
  proceduralFormDefinitionSource : HousingRegressionSourceRole
  caseFactualOutcomeSource : HousingRegressionSourceRole

record HousingRegressionAttributedSource : Set₁ where
  constructor housingRegressionAttributedSource
  field
    role : HousingRegressionSourceRole
    sourceReference : String
    propositionReference : String
    sourceReceipt : Set

open HousingRegressionAttributedSource public

s185AttributedSource : Set → HousingRegressionAttributedSource
s185AttributedSource receipt =
  housingRegressionAttributedSource
    legalTestDefinitionSource
    s185SourceReference
    "continuing lessor maintenance / good-repair duty"
    receipt

form11ProcedureAttributedSource : Set → HousingRegressionAttributedSource
form11ProcedureAttributedSource receipt =
  housingRegressionAttributedSource
    proceduralFormDefinitionSource
    form11ProceduralSourceReference
    "Form 11 is the prescribed notice-to-remedy-breach procedure"
    receipt

brightonFactAttributedSource : Set → HousingRegressionAttributedSource
brightonFactAttributedSource receipt =
  housingRegressionAttributedSource
    caseFactualOutcomeSource
    brightonForm11CarrierReference
    brightonTargetFactReference
    receipt

------------------------------------------------------------------------
-- MATTER-LEVEL INPUT
--
-- The new #850 directional bridge still owns source support -> applicability.
-- The existing violation meet still owns applicability -> violation.  This
-- module fixes the matter/source/test coordinates and requires explicit
-- same-object receipts at every transition.
------------------------------------------------------------------------

record BrightonS185HousingRegressionInput
    {residual : Source.NatSourceSupportResidual}
    {demand : Verify.SourceVerificationDemand residual}
    (verification : Verify.SourceVerificationReceipt demand)
    (admission : Verify.SourceSupportAdmission verification)
    (state : Status.SemanticCommitmentState) : Set₁ where
  constructor brightonS185HousingRegressionInput
  field
    brightonEpisode : Housing.HousingEpisode
    episodeReferenceIsBrighton :
      Housing.episodeReference brightonEpisode ≡ brightonEpisodeReference
    premisesReferenceIsBrighton :
      Housing.premisesReference brightonEpisode ≡ brightonPremisesReference

    factualSource : HousingRegressionAttributedSource
    factualSourceRoleIsCaseSource :
      role factualSource ≡ caseFactualOutcomeSource
    factualSourceCarrierIsBrightonForm11 :
      sourceReference factualSource ≡ brightonForm11CarrierReference
    factualPropositionIsExact :
      propositionReference factualSource ≡ brightonTargetFactReference

    legalDefinitionSource : HousingRegressionAttributedSource
    legalDefinitionRoleIsPrimaryTestDefinition :
      role legalDefinitionSource ≡ legalTestDefinitionSource
    legalDefinitionIsS185 :
      sourceReference legalDefinitionSource ≡ s185SourceReference
    historicalS185AuthorityAt24Jan2023 : Set

    form11ProcedureSource : HousingRegressionAttributedSource
    form11ProcedureRoleIsProcedure :
      role form11ProcedureSource ≡ proceduralFormDefinitionSource
    form11ProcedureIsS325Form11 :
      sourceReference form11ProcedureSource ≡ form11ProceduralSourceReference

    directionalApplicabilityInput :
      Directional.SourceConditionedApplicabilityMeetInput
        {residual} {demand} verification admission state

    factualCarrierMatchesDirectionalSourceArtifact : Set
    exactFactMatchesDirectionalTargetProposition : Set
    legalMeetTargetsS185Issue : Set
    jurisdictionIsQueenslandReceipt : Set
    temporalScopeIncludes24Jan2023Receipt : Set

    violationInput : ViolationMeet.ViolationMeetInput state
    violationUsesCompiledApplicability :
      ViolationMeet.receipt
        (ViolationMeet.applicability
          (ViolationMeet.prerequisites violationInput))
      ≡ Directional.compileSourceConditionedApplicability
          directionalApplicabilityInput

    violationDecisionReference : String
    violationDecisionIsCaseSpecific : Set

open BrightonS185HousingRegressionInput public

compileBrightonS185Applicability :
  ∀ {residual demand verification admission state} →
  BrightonS185HousingRegressionInput
    {residual} {demand} verification admission state →
  Legal.WrongTypeApplicabilityReceipt
compileBrightonS185Applicability input =
  Directional.compileSourceConditionedApplicability
    (directionalApplicabilityInput input)

compileBrightonS185Violation :
  ∀ {residual demand verification admission state} →
  BrightonS185HousingRegressionInput
    {residual} {demand} verification admission state →
  Legal.ViolationReceipt
compileBrightonS185Violation input =
  ViolationMeet.compileViolationMeet (violationInput input)

compiledBrightonApplicabilityIsExactlyViolationInputApplicability :
  ∀ {residual demand verification admission state}
    (input : BrightonS185HousingRegressionInput
      {residual} {demand} verification admission state) →
  ViolationMeet.receipt
    (ViolationMeet.applicability
      (ViolationMeet.prerequisites (violationInput input)))
  ≡ compileBrightonS185Applicability input
compiledBrightonApplicabilityIsExactlyViolationInputApplicability input =
  violationUsesCompiledApplicability input

------------------------------------------------------------------------
-- REGRESSION FIREWALLS
------------------------------------------------------------------------

data Form11AssertionDefinesS185 : Set where
data Form11AssertionAutomaticallyProvesViolation : Set where
data PositiveFactSupportAutomaticallyProvesApplicability : Set where
data ApplicabilityAutomaticallyProvesViolation : Set where
data BrightonViolationAutomaticallyProvesLiability : Set where
data BrightonEpisodeAutomaticallyProvesLongitudinalPattern : Set where

data HealthContextAutomaticallyProvesHousingCausation : Set where

form11AssertionDoesNotDefineS185 : Form11AssertionDefinesS185 → ⊥
form11AssertionDoesNotDefineS185 ()

form11AssertionDoesNotAutomaticallyProveViolation :
  Form11AssertionAutomaticallyProvesViolation → ⊥
form11AssertionDoesNotAutomaticallyProveViolation ()

positiveFactSupportDoesNotAutomaticallyProveApplicability :
  PositiveFactSupportAutomaticallyProvesApplicability → ⊥
positiveFactSupportDoesNotAutomaticallyProveApplicability ()

applicabilityDoesNotAutomaticallyProveViolation :
  ApplicabilityAutomaticallyProvesViolation → ⊥
applicabilityDoesNotAutomaticallyProveViolation ()

brightonViolationDoesNotAutomaticallyProveLiability :
  BrightonViolationAutomaticallyProvesLiability → ⊥
brightonViolationDoesNotAutomaticallyProveLiability ()

brightonEpisodeDoesNotAutomaticallyProveLongitudinalPattern :
  BrightonEpisodeAutomaticallyProvesLongitudinalPattern → ⊥
brightonEpisodeDoesNotAutomaticallyProveLongitudinalPattern ()

healthContextDoesNotAutomaticallyProveHousingCausation :
  HealthContextAutomaticallyProvesHousingCausation → ⊥
healthContextDoesNotAutomaticallyProveHousingCausation ()

record BrightonS185HousingRegressionBoundary : Set where
  constructor brighton-s185-housing-regression-boundary
  field
    oneEpisodeOnly : Bool
    sourceTestDefinitionSeparatedFromCaseOutcome : Bool
    exactFactualCarrierIdentityRequired : Bool
    exactPropositionIdentityRequired : Bool
    historicalAuthorityReceiptRequired : Bool
    jurisdictionReceiptRequired : Bool
    temporalScopeReceiptRequired : Bool
    directionalApplicabilityBridgeReused : Bool
    existingViolationMeetReused : Bool
    exactApplicabilityReceiptReusedByViolation : Bool
    form11AssertionDefinesLegalTest : Bool
    form11AssertionAutomaticallyProvesViolation : Bool
    positiveFactSupportAutomaticallyProvesApplicability : Bool
    applicabilityAutomaticallyProvesViolation : Bool
    violationAutomaticallyProvesLiability : Bool
    oneEpisodeAutomaticallyProvesSystemicPattern : Bool
    healthContextAutomaticallyProvesCausation : Bool

canonicalBrightonS185HousingRegressionBoundary :
  BrightonS185HousingRegressionBoundary
canonicalBrightonS185HousingRegressionBoundary =
  brighton-s185-housing-regression-boundary
    true true true true true true true true true true
    false false false false false false false
