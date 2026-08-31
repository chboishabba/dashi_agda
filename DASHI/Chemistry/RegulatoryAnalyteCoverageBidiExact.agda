module DASHI.Chemistry.RegulatoryAnalyteCoverageBidiExact where

------------------------------------------------------------------------
-- REGULATORY ANALYTE COVERAGE / CHEMICAL-STATE BIDI BOUNDARY
--
-- Regulatory source:
--   Therapeutic Goods (Standard for Medicinal Cannabis) (TGO 93) Order 2017,
--   Schedule 1: pesticides are assessed under Ph Eur 2.8.13.
--
-- European Pharmacopoeia correction important to this revision:
--   Ph Eur 2.8.13 is not merely one closed blacklist.  Table 2.8.13.-1 gives
--   explicit pesticide limits, while suspected pesticides not in that table
--   are routed to Regulation (EC) No 396/2005; if absent there too, an
--   ADI-based calculated limit is specified.
--
-- User-supplied social-media screenshot, 2026-08-31:
--   visible slide text includes a claim that the Australian system was
--   "gamed" in about 45 minutes.  The screenshot is an application/claim
--   surface only: it neither owns the generic assay-stress method nor proves a
--   real bypass.
--
-- The finite non-factorability results below are DASHI theorems.  They are not
-- attributed to TGA, the European Pharmacopoeia, or the screenshot speaker.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NonFactor

------------------------------------------------------------------------
-- Keep source role distinct from proposition status.
------------------------------------------------------------------------

data SourceKind : Set where
  legislativeStandard regulatorGuidance pharmacopoeiaText socialMediaScreenshot : SourceKind

data SourceRole : Set where
  normativeRequirement guidanceStatement methodText speakerAssertion : SourceRole

data VerificationStatus : Set where
  sourceTextRecovered independentlyEstablished unresolved : VerificationStatus

record SourceAttribution : Set where
  constructor sourceAttribution
  field
    sourceKind : SourceKind
    sourceRole : SourceRole
    verificationStatus : VerificationStatus
    reference : String

open SourceAttribution public

------------------------------------------------------------------------
-- Regulatory scope, actual assay scope and full chemical state are separate.
-- `offPanelCompound` means outside the synthetic finite assay surface below;
-- it MUST NOT be read as `no Ph Eur/TGO regulatory limit route`.
------------------------------------------------------------------------

data Analyte : Set where
  regulatedPesticideA regulatedPesticideB offPanelCompound : Analyte

data ScopeStatus : Set where
  inScope outOfScope : ScopeStatus

data Presence : Set where
  absent present : Presence

data ComplianceResult : Set where
  compliancePass complianceFail : ComplianceResult

data DetectionResult : Set where
  notDetected detected : DetectionResult

data LegalStatus : Set where
  noViolationEstablished violationEstablished : LegalStatus

record RegulatoryPanel : Set where
  constructor regulatoryPanel
  field
    regulatedScope : Analyte → ScopeStatus
    methodReference : String
    limitsReference : String

open RegulatoryPanel public

record AssayPanel : Set where
  constructor assayPanel
  field
    assayScope : Analyte → ScopeStatus
    assayReference : String

open AssayPanel public

record ChemicalState : Set where
  constructor chemicalState
  field
    presence : Analyte → Presence

open ChemicalState public

record BatchObservation : Set where
  constructor batchObservation
  field
    regulatoryResult : ComplianceResult
    assayResult : Analyte → DetectionResult

open BatchObservation public

------------------------------------------------------------------------
-- A compliance observation is a projection, not the whole chemical state.
------------------------------------------------------------------------

data FineBatch : Set where
  cleanPassingBatch offPanelPresentPassingBatch : FineBatch

complianceSurface : FineBatch → ComplianceResult
complianceSurface cleanPassingBatch = compliancePass
complianceSurface offPanelPresentPassingBatch = compliancePass

offPanelPresence : FineBatch → Presence
offPanelPresence cleanPassingBatch = absent
offPanelPresence offPanelPresentPassingBatch = present

samePassDifferentOffPanelPresence :
  NonFactor.NonFactorabilityWitness complianceSurface offPanelPresence
samePassDifferentOffPanelPresence =
  NonFactor.nonFactorabilityWitness
    cleanPassingBatch
    offPanelPresentPassingBatch
    refl
    (λ ())

complianceCannotRecoverCompleteOffPanelState :
  NonFactor.FactorsThrough complianceSurface offPanelPresence → ⊥
complianceCannotRecoverCompleteOffPanelState =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    samePassDifferentOffPanelPresence

------------------------------------------------------------------------
-- Re-labelling a pass result cannot recover erased chemistry.
------------------------------------------------------------------------

record ComplianceCertificate : Set where
  constructor complianceCertificate
  field
    certificateText : String

renderCertificate : ComplianceResult → ComplianceCertificate
renderCertificate compliancePass = complianceCertificate "passes declared compliance observation"
renderCertificate complianceFail = complianceCertificate "fails declared compliance observation"

certificateCannotRecoverCompleteOffPanelState :
  NonFactor.FactorsThrough
    (λ batch → renderCertificate (complianceSurface batch))
    offPanelPresence → ⊥
certificateCannotRecoverCompleteOffPanelState =
  NonFactor.rechartingCannotRecoverErasedPhenomenon
    renderCertificate samePassDifferentOffPanelPresence

------------------------------------------------------------------------
-- Detection, regulatory route and legal conclusion are distinct questions.
------------------------------------------------------------------------

data CompoundObservation : Set where
  unlistedUndetected unlistedDetected : CompoundObservation

detectionOf : CompoundObservation → DetectionResult
detectionOf unlistedUndetected = notDetected
detectionOf unlistedDetected = detected

legalStatusOf : CompoundObservation → LegalStatus
legalStatusOf unlistedUndetected = noViolationEstablished
legalStatusOf unlistedDetected = noViolationEstablished

detectionDoesNotManufactureViolation :
  legalStatusOf unlistedDetected ≡ noViolationEstablished
detectionDoesNotManufactureViolation = refl

-- Invalid automatic promotions remain uninhabited.
data PassImpliesUniversalChemicalAbsencePermission : Set where
data OffPanelImpliesUndetectablePermission : Set where
data DetectionImpliesViolationPermission : Set where
data SocialMediaAssertionImpliesVerifiedBypassPermission : Set where
data NotExplicitTableMemberImpliesNoRegulatoryLimitPermission : Set where

passCannotAutoPromoteToUniversalChemicalAbsence :
  PassImpliesUniversalChemicalAbsencePermission → ⊥
passCannotAutoPromoteToUniversalChemicalAbsence ()

offPanelCannotAutoPromoteToUndetectable :
  OffPanelImpliesUndetectablePermission → ⊥
offPanelCannotAutoPromoteToUndetectable ()

detectionCannotAutoPromoteToViolation :
  DetectionImpliesViolationPermission → ⊥
detectionCannotAutoPromoteToViolation ()

socialMediaAssertionCannotAutoPromoteToVerifiedBypass :
  SocialMediaAssertionImpliesVerifiedBypassPermission → ⊥
socialMediaAssertionCannotAutoPromoteToVerifiedBypass ()

notExplicitTableMemberCannotAutoPromoteToNoRegulatoryLimit :
  NotExplicitTableMemberImpliesNoRegulatoryLimitPermission → ⊥
notExplicitTableMemberCannotAutoPromoteToNoRegulatoryLimit ()

------------------------------------------------------------------------
-- Source-bounded TGO 93 / TGA / Ph Eur calibration.
------------------------------------------------------------------------

tgo93PesticideRequirement : SourceAttribution
tgo93PesticideRequirement =
  sourceAttribution
    legislativeStandard
    normativeRequirement
    sourceTextRecovered
    "TGO 93 Schedule 1 item 5: Pesticides; Ph Eur 2.8.13; not more than the limits specified in Ph Eur 2.8.13"

tgaQualityGuidance : SourceAttribution
tgaQualityGuidance =
  sourceAttribution
    regulatorGuidance
    guidanceStatement
    sourceTextRecovered
    "TGA: Complying with the quality requirements for medicinal cannabis"

phEurUnlistedPesticideRoute : SourceAttribution
phEurUnlistedPesticideRoute =
  sourceAttribution
    pharmacopoeiaText
    methodText
    sourceTextRecovered
    "Ph Eur 11.0 2.8.13: suspected pesticides outside Table 2.8.13.-1 use EU 396/2005 limits; if absent from EU texts, an ADI-based calculated limit applies"

userSuppliedSlideAssertion : SourceAttribution
userSuppliedSlideAssertion =
  sourceAttribution
    socialMediaScreenshot
    speakerAssertion
    unresolved
    "User-supplied screenshot 2026-08-31: visible slide claims system gaming in about 45 minutes"

------------------------------------------------------------------------
-- Synthetic assay panel retained only as the finite logical calibration used by
-- the non-factorability theorem.  It is no longer named `canonicalTGO93Panel`:
-- doing so would incorrectly equate this three-analyte toy with the legal Ph Eur
-- limit architecture.
------------------------------------------------------------------------

syntheticDeclaredAssayPanel : AssayPanel
syntheticDeclaredAssayPanel =
  assayPanel
    scope
    "DASHI synthetic three-coordinate assay observer; not a real laboratory panel"
  where
    scope : Analyte → ScopeStatus
    scope regulatedPesticideA = inScope
    scope regulatedPesticideB = inScope
    scope offPanelCompound = outOfScope

------------------------------------------------------------------------
-- Real positive table-membership receipts now live in the sibling owner:
--   DASHI.Chemistry.TGO93PhEurPesticideMembershipExact
-- including DDT, acephate, chlorpyriphos-ethyl and other named entries.
------------------------------------------------------------------------

record RegulatoryAnalyteCoverageBoundary : Set where
  constructor regulatoryAnalyteCoverageBoundary
  field
    tgo93ReferencesPhEur2813ForPesticides : Bool
    regulatoryComplianceIsCompleteChemicalCharacterisation : Bool
    offPanelMeansZeroDetectionProbability : Bool
    detectedUnlistedCompoundAutomaticallyViolatesLaw : Bool
    socialMediaSlideEstablishesSuccessfulBypass : Bool
    socialMediaSlideOwnsGenericStressAuditMethod : Bool
    notExplicitTableMemberMeansNoRegulatoryLimit : Bool
    realNamedPositiveMembershipReceiptsInstalledInChemistry : Bool
    finiteNonFactorabilityIsDASHITheorem : Bool

canonicalRegulatoryAnalyteCoverageBoundary : RegulatoryAnalyteCoverageBoundary
canonicalRegulatoryAnalyteCoverageBoundary =
  regulatoryAnalyteCoverageBoundary
    true
    false
    false
    false
    false
    false
    false
    true
    true
