module DASHI.Chemistry.RegulatoryAnalyteCoverageBidiExact where

------------------------------------------------------------------------
-- REGULATORY ANALYTE COVERAGE / CHEMICAL-STATE BIDI BOUNDARY
--
-- Source attribution is deliberately layered.
--
-- Regulatory source:
--   Therapeutic Goods (Standard for Medicinal Cannabis) (TGO 93) Order 2017,
--   Schedule 1: pesticides are assessed against the limits in Ph Eur 2.8.13.
--   https://www.legislation.gov.au/
--
-- Regulator guidance:
--   Therapeutic Goods Administration,
--   "Complying with the quality requirements for medicinal cannabis"
--   (last updated 14 Oct 2024 at the time this module was written).
--   The guidance describes TGO 93 as minimum quality requirements, permits
--   justified reduced/rotational testing on GMP grounds, allows suitably
--   validated alternative methods, and notes that additional testing may be
--   appropriate in some circumstances.
--   https://www.tga.gov.au/resources/guidance/complying-quality-requirements-medicinal-cannabis
--
-- User-supplied social-media screenshot, 2026-08-31:
--   visible slide text includes "Statistical probability chemists like myself
--   have gamed your system" and "Took me about 45 minutes".
--
-- The screenshot is evidence only of the visible assertion.  This module does
-- NOT authenticate the speaker, establish the claimed bypass, identify an
-- actual pesticide, or treat the social-media claim as empirical verification.
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
  legislativeStandard regulatorGuidance socialMediaScreenshot : SourceKind

data SourceRole : Set where
  normativeRequirement guidanceStatement speakerAssertion : SourceRole

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
renderCertificate compliancePass = complianceCertificate "passes declared regulatory pesticide specification"
renderCertificate complianceFail = complianceCertificate "fails declared regulatory pesticide specification"

certificateCannotRecoverCompleteOffPanelState :
  NonFactor.FactorsThrough
    (λ batch → renderCertificate (complianceSurface batch))
    offPanelPresence → ⊥
certificateCannotRecoverCompleteOffPanelState =
  NonFactor.rechartingCannotRecoverErasedPhenomenon
    renderCertificate samePassDifferentOffPanelPresence

------------------------------------------------------------------------
-- Three distinct questions:
--   1. was a compound detected?
--   2. is it within a declared regulatory/assay scope?
--   3. does its presence establish a legal violation under an applicable rule?
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

-- Empty permission types make the invalid promotions uninhabited unless an
-- application supplies a separate legal/normative bridge outside this module.
data PassImpliesUniversalChemicalAbsencePermission : Set where
data OffPanelImpliesUndetectablePermission : Set where
data DetectionImpliesViolationPermission : Set where
data SocialMediaAssertionImpliesVerifiedBypassPermission : Set where

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

------------------------------------------------------------------------
-- Source-bounded TGO 93 / TGA calibration.
------------------------------------------------------------------------

tgo93PesticideRequirement : SourceAttribution
tgo93PesticideRequirement =
  sourceAttribution
    legislativeStandard
    normativeRequirement
    sourceTextRecovered
    "TGO 93 Schedule 1: pesticides; limits specified in Ph Eur 2.8.13"

tgaQualityGuidance : SourceAttribution
tgaQualityGuidance =
  sourceAttribution
    regulatorGuidance
    guidanceStatement
    sourceTextRecovered
    "TGA: Complying with the quality requirements for medicinal cannabis"

userSuppliedSlideAssertion : SourceAttribution
userSuppliedSlideAssertion =
  sourceAttribution
    socialMediaScreenshot
    speakerAssertion
    unresolved
    "User-supplied screenshot 2026-08-31: visible slide claims system gaming in about 45 minutes"

canonicalTGO93Panel : RegulatoryPanel
canonicalTGO93Panel =
  regulatoryPanel
    scope
    "Ph Eur 2.8.13"
    "TGO 93 Schedule 1 limits specified in Ph Eur 2.8.13"
  where
    scope : Analyte → ScopeStatus
    scope regulatedPesticideA = inScope
    scope regulatedPesticideB = inScope
    scope offPanelCompound = outOfScope

------------------------------------------------------------------------
-- Important calibration boundary:
-- `offPanelCompound` is a synthetic finite witness.  It is NOT the name of an
-- actual pesticide alleged to be absent from Ph Eur 2.8.13.  Establishing that
-- a real compound is outside an applicable method/panel requires a separate,
-- edition-specific analytical receipt.
------------------------------------------------------------------------

record RegulatoryAnalyteCoverageBoundary : Set where
  constructor regulatoryAnalyteCoverageBoundary
  field
    tgo93ReferencesPhEur2813ForPesticides : Bool
    regulatoryComplianceIsCompleteChemicalCharacterisation : Bool
    offPanelMeansZeroDetectionProbability : Bool
    detectedUnlistedCompoundAutomaticallyViolatesLaw : Bool
    socialMediaSlideEstablishesSuccessfulBypass : Bool
    exactPanelMembershipForRealNamedCompoundsInstalledHere : Bool
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
    true
