module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSupportingMaterialManifestationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSparseCalibrationFibreExact as Sparse

------------------------------------------------------------------------
-- ADK SUPPORTING-MATERIAL MANIFESTATION IDENTITY GUARD
--
-- Acquisition discovered a source-manifestation mismatch that must be retained
-- before any Figure-5 / supporting-material numeral is promoted into the sparse
-- calibration fibre.
--
-- The AdK article identity is:
--   DOI   10.1016/j.bpj.2015.06.059
--   PMID  26244746
--   PMCID PMC4572606
--   PII   S0006349515006700  (formatted S0006-3495(15)00670-0)
--
-- The PMC-rendered footnote currently exposes a legacy supplemental URL ending
--   S0006-3495(15)00617-7
-- but PubMed identifies that PII with the different article
--   "Isocost Lines Describe the Cellular Economy of Genetic Circuits"
--   DOI 10.1016/j.bpj.2015.06.034, PMID 26244745, PMCID PMC4572570.
--
-- DASHI therefore records a cross-source manifestation mismatch.  It does not
-- diagnose how the mismatch arose, rewrite either source, or use the foreign
-- supplement to pay AdK numeric cells.  The PMC AdK page's attached Document S1
-- / mmc1.pdf and Document S2 / mmc2.pdf remain candidate same-article
-- manifestations, but exact numeric promotion still needs a trustworthy
-- machine-readable or separately receipted figure/table readout.
------------------------------------------------------------------------

adkArticleSource : Attribution.AttributedSource
adkArticleSource = Sparse.liLiuJi2015Source

adkArticleReceipt : Snowball.SourceRoleSnowballReceipt adkArticleSource
adkArticleReceipt = Snowball.canonicalSourceRoleSnowballReceipt adkArticleSource

isocostSource : Attribution.AttributedSource
isocostSource =
  Attribution.mkDOISource
    "Gyorgy, Jimenez, Yazbek, Huang, Chung, Weiss and Del Vecchio"
    "Isocost Lines Describe the Cellular Economy of Genetic Circuits"
    "Biophysical Journal"
    "2015"
    "10.1016/j.bpj.2015.06.034"
    "https://pubmed.ncbi.nlm.nih.gov/26244745/"
    Attribution.academicArticleSource
    "pays identity of the article associated with PII S0006-3495(15)00617-7; it has no adenylate-kinase calibration authority"
    Attribution.publicAttribution

isocostReceipt : Snowball.SourceRoleSnowballReceipt isocostSource
isocostReceipt = Snowball.canonicalSourceRoleSnowballReceipt isocostSource

------------------------------------------------------------------------
-- Stable identity coordinates.
------------------------------------------------------------------------

adkDOI : Identity.ExternalIdentityDemand
adkDOI = Identity.mkOptionalIdentityDemand
  "AdK supporting-material manifestation guard"
  "AdK article DOI"
  "Mapping the Dynamics Landscape of Conformational Transitions in Enzyme: The Adenylate Kinase Case"
  Identity.doi
  (Identity.verified "10.1016/j.bpj.2015.06.059" "PubMed/PMC/OpenAlex article identity")

adkPII : Identity.ExternalIdentityDemand
adkPII = Identity.mkOptionalIdentityDemand
  "AdK supporting-material manifestation guard"
  "AdK article PII"
  "Mapping the Dynamics Landscape of Conformational Transitions in Enzyme: The Adenylate Kinase Case"
  Identity.officialIdentifier
  (Identity.verified "S0006349515006700" "ScienceDirect/OpenAlex article identity; formatted PII S0006-3495(15)00670-0")

legacyFootnotePII : Identity.ExternalIdentityDemand
legacyFootnotePII = Identity.mkOptionalIdentityDemand
  "AdK supporting-material manifestation guard"
  "PII embedded in PMC-rendered AdK legacy supplemental URL"
  "S0006-3495(15)00617-7"
  Identity.officialIdentifier
  (Identity.verified "S0006-3495(15)00617-7" "observed in the PMC-rendered AdK supporting-material footnote")

foreignPIIArticle : Identity.ExternalIdentityDemand
foreignPIIArticle = Identity.mkOptionalIdentityDemand
  "AdK supporting-material manifestation guard"
  "article identity resolved from legacy supplemental PII"
  "Isocost Lines Describe the Cellular Economy of Genetic Circuits"
  Identity.officialIdentifier
  (Identity.verified "PMID 26244745 / DOI 10.1016/j.bpj.2015.06.034" "PubMed identifies PII S0006-3495(15)00617-7 with this different article")

------------------------------------------------------------------------
-- Manifestation role separation.
------------------------------------------------------------------------

data ManifestationRole : Set where
  articleIdentityManifestation : ManifestationRole
  legacyFootnoteLocator : ManifestationRole
  pmcAttachedSupplement : ManifestationRole
  foreignArticleManifestation : ManifestationRole
  unverifiedVisualReadout : ManifestationRole

record SupportingMaterialManifestation : Set where
  constructor supporting-material-manifestation
  field
    label : String
    locator : String
    role : ManifestationRole
    assertedArticleReference : String
    sameAdkArticlePaid : Bool
    mayPayAdkCalibrationNumber : Bool
open SupportingMaterialManifestation public

adkArticleManifestation : SupportingMaterialManifestation
adkArticleManifestation = supporting-material-manifestation
  "AdK article"
  "DOI 10.1016/j.bpj.2015.06.059 / PMCID PMC4572606 / PII S0006349515006700"
  articleIdentityManifestation
  "Li-Liu-Ji 2015 AdK article"
  true false

legacyFootnoteManifestation : SupportingMaterialManifestation
legacyFootnoteManifestation = supporting-material-manifestation
  "PMC-rendered legacy supplemental URL"
  "http://www.biophysj.org/biophysj/supplemental/S0006-3495(15)00617-7"
  legacyFootnoteLocator
  "string occurs on the AdK PMC rendering, but its terminal PII resolves to another article"
  false false

pmcDocumentS1Manifestation : SupportingMaterialManifestation
pmcDocumentS1Manifestation = supporting-material-manifestation
  "PMC AdK Document S1"
  "PMC4572606 Supporting Material: mmc1.pdf"
  pmcAttachedSupplement
  "Supporting Materials and Methods, 18 figures, and four tables attached to the AdK PMC record"
  true false

pmcDocumentS2Manifestation : SupportingMaterialManifestation
pmcDocumentS2Manifestation = supporting-material-manifestation
  "PMC AdK Document S2"
  "PMC4572606 Supporting Material: mmc2.pdf"
  pmcAttachedSupplement
  "article plus supporting material attached to the AdK PMC record"
  true false

foreignIsocostManifestation : SupportingMaterialManifestation
foreignIsocostManifestation = supporting-material-manifestation
  "foreign article resolved from legacy PII"
  "PII S0006-3495(15)00617-7 / PMID 26244745"
  foreignArticleManifestation
  "Isocost Lines Describe the Cellular Economy of Genetic Circuits"
  false false

------------------------------------------------------------------------
-- Acquisition gate.
------------------------------------------------------------------------

data NumericAcquisitionMethod : Set where
  machineReadableArticleText : NumericAcquisitionMethod
  machineReadableSupplementText : NumericAcquisitionMethod
  separatelyReceiptedFigureReadout : NumericAcquisitionMethod
  unverifiedVisualGuess : NumericAcquisitionMethod
  foreignSupplementReadout : NumericAcquisitionMethod

record NumericAcquisitionGate : Set where
  constructor numeric-acquisition-gate
  field
    targetArticle : String
    targetManifestation : SupportingMaterialManifestation
    method : NumericAcquisitionMethod
    sameObjectManifestationPaid : Bool
    locatorSpecificReceiptPaid : Bool
    numericPromotionAllowed : Bool
    interpretation : String
open NumericAcquisitionGate public

legacyFootnoteAcquisitionGate : NumericAcquisitionGate
legacyFootnoteAcquisitionGate = numeric-acquisition-gate
  "Li-Liu-Ji 2015 AdK"
  legacyFootnoteManifestation
  foreignSupplementReadout
  false false false
  "fail closed: the embedded PII resolves to another article, so this locator cannot pay AdK numeric calibration"

pmcDocumentS1AcquisitionGate : NumericAcquisitionGate
pmcDocumentS1AcquisitionGate = numeric-acquisition-gate
  "Li-Liu-Ji 2015 AdK"
  pmcDocumentS1Manifestation
  machineReadableSupplementText
  true false false
  "same-article supplement candidate retained; numeric promotion remains blocked until a concrete machine-readable value/locator receipt is acquired"

figureFiveVisualGate : NumericAcquisitionGate
figureFiveVisualGate = numeric-acquisition-gate
  "Li-Liu-Ji 2015 AdK"
  adkArticleManifestation
  unverifiedVisualGuess
  true false false
  "Figure 5 existence and units are source-paid, but unreceipted visual transcription/OCR-style guessing cannot pay individual numeric cells"

------------------------------------------------------------------------
-- WrongType / source-identity firewalls.
------------------------------------------------------------------------

data LegacyFootnoteStringCreatesSameObjectSupplement : Set where
data ForeignPIICreatesAdkCalibrationAuthority : Set where
data SamePmcPageCreatesNumericPayment : Set where
data FigureExistenceCreatesNumericLabel : Set where

legacyFootnoteDoesNotCreateSameObjectSupplement :
  LegacyFootnoteStringCreatesSameObjectSupplement → ⊥
legacyFootnoteDoesNotCreateSameObjectSupplement ()

foreignPiiDoesNotCreateAdkCalibrationAuthority :
  ForeignPIICreatesAdkCalibrationAuthority → ⊥
foreignPiiDoesNotCreateAdkCalibrationAuthority ()

samePmcPageDoesNotCreateNumericPayment : SamePmcPageCreatesNumericPayment → ⊥
samePmcPageDoesNotCreateNumericPayment ()

figureExistenceDoesNotCreateNumericLabel : FigureExistenceCreatesNumericLabel → ⊥
figureExistenceDoesNotCreateNumericLabel ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record SupportingMaterialManifestationBoundary : Set where
  constructor supporting-material-manifestation-boundary
  field
    adkArticleIdentityPaid : Bool
    legacyFootnotePiiObserved : Bool
    legacyFootnotePiiResolvesToDifferentArticle : Bool
    pmcAttachedSupportingMaterialRetained : Bool
    machineReadableSourcePreferred : Bool
    sameObjectManifestationRequiredBeforeNumericPromotion : Bool
    legacyFootnoteMayPayAdkSupplement : Bool
    foreignSupplementMayPayCalibrationNumber : Bool
    unverifiedFigureReadoutMayPayNumericCell : Bool
    mismatchDiagnosedAsPublisherError : Bool
    mismatchErasedByDashi : Bool
    nextResidual : String
open SupportingMaterialManifestationBoundary public

canonicalSupportingMaterialManifestationBoundary : SupportingMaterialManifestationBoundary
canonicalSupportingMaterialManifestationBoundary = supporting-material-manifestation-boundary
  true true true true true true
  false false false false false
  "acquire the actual PMC-attached AdK Document S1/S2 or another same-article machine-readable manifestation and bind each Figure-5/Table-S value to an exact locator before upgrading SparseNumericCoordinate cells. Retain the legacy PII collision as provenance; do not diagnose a publisher cause or import the foreign Isocost supplement."
