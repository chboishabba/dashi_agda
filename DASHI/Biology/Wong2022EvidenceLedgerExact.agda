module DASHI.Biology.Wong2022EvidenceLedgerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Biology.Wong2022LysergicAcidFiniteCore as Core
import DASHI.Biology.Wong2022LysergicAcidEvidenceExact as Wong
import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- SOURCE-SCOPED EVIDENCE LEDGER / NON-OPERATIONAL CROSSWALK.
-- Primary research: Wong, Lim, Tan, Go, Bell, Freemont, Yew (2022),
-- Nature Communications 13:712, DOI 10.1038/s41467-022-28386-6.
-- Data-locator claims are paper statements, not independent re-analysis.
-- Source workbook / supplement bytes are not available to this receipt.
------------------------------------------------------------------------

data PaperLocator : Set where
  articleAbstract : PaperLocator
  articleResults : PaperLocator
  figureFive : PaperLocator
  figureSix : PaperLocator
  supplementaryFigureFourteen : PaperLocator
  supplementaryTableEleven : PaperLocator
  supplementaryTableTwelve : PaperLocator
  isotopeTracingParagraph : PaperLocator

data DataReceiptState : Set where
  paperTextObserved : DataReceiptState
  supplementaryDataNotInspected : DataReceiptState
  independentlyReanalysed : DataReceiptState

record IndexedEndpoint (scale : Core.ReportedScale) : Set where
  constructor indexedEndpoint
  field
    measurement : Wong.ReportedEndpoint scale
    primaryLocator : PaperLocator
    secondaryLocator : PaperLocator
    replicateCountReportedInFigureCaption : Nat
    reportedUnit : String
    dataReceipt : DataReceiptState

    rawMeasurementTableReviewed : Bool
    rawMeasurementTableReviewedIsFalse :
      rawMeasurementTableReviewed ≡ false

    uncertaintyNumbersLoaded : Bool
    uncertaintyNumbersLoadedIsFalse :
      uncertaintyNumbersLoaded ≡ false

open IndexedEndpoint public

oneLitreIndexed : IndexedEndpoint Core.oneLitreBioreactor
oneLitreIndexed =
  indexedEndpoint
    Wong.oneLitreEndpoint
    figureSix
    supplementaryTableTwelve
    3
    "mg/L"
    supplementaryDataNotInspected
    false refl
    false refl

fourLitreIndexed : IndexedEndpoint Core.fourLitreBioreactor
fourLitreIndexed =
  indexedEndpoint
    Wong.fourLitreEndpoint
    figureSix
    supplementaryTableTwelve
    3
    "mg/L"
    supplementaryDataNotInspected
    false refl
    false refl

record LocatedAnalyticalClaim : Set where
  constructor locatedAnalyticalClaim
  field
    evidence : Wong.SourceReportedEvidence
    paperLocator : PaperLocator
    dataReceipt : DataReceiptState

    independentInstrumentOrRawDataReview : Bool
    independentInstrumentOrRawDataReviewIsFalse :
      independentInstrumentOrRawDataReview ≡ false

massSpectrometryClaim : LocatedAnalyticalClaim
massSpectrometryClaim =
  locatedAnalyticalClaim
    Wong.paperIdentityEvidence
    figureFive
    paperTextObserved
    false refl

nmrClaim : LocatedAnalyticalClaim
nmrClaim =
  locatedAnalyticalClaim
    Wong.paperNmrEvidence
    supplementaryTableEleven
    supplementaryDataNotInspected
    false refl

originClaim : LocatedAnalyticalClaim
originClaim =
  locatedAnalyticalClaim
    Wong.paperOriginEvidence
    isotopeTracingParagraph
    paperTextObserved
    false refl

------------------------------------------------------------------------
-- PUBCHEM / CHEBI: authority-labelled candidate, not same sample identity.
-- CID 6717 and CHEBI:6604 are displayed in PubChem's external-reference
-- record. Stereochemical and specimen-level equivalence still needs
-- independently reviewed source and structure/charge/tautomer conditions.
------------------------------------------------------------------------

data RegistryRelationStatus : Set where
  sourceRegistryCrossReference : RegistryRelationStatus
  reviewedSameObjectIdentity : RegistryRelationStatus

record CandidateRegistryCrossReference : Set where
  constructor candidateRegistryCrossReference
  field
    subject : Core.NamedMolecule
    registrySource : Source.AttributedSource
    pubChemCID : String
    chEBIIdentifier : String
    chemicalFormula : String
    registryRelation : RegistryRelationStatus
    reviewRequired : Bool
    reviewRequiredIsTrue : reviewRequired ≡ true
    assaySpecimenIdentityPaid : Bool
    assaySpecimenIdentityPaidIsFalse :
      assaySpecimenIdentityPaid ≡ false

candidateDLARegistryCrossReference : CandidateRegistryCrossReference
candidateDLARegistryCrossReference =
  candidateRegistryCrossReference
    Core.dLysergicAcid
    Wong.pubChemLysergicAcid
    "6717"
    "CHEBI:6604"
    "C16H16N2O2"
    sourceRegistryCrossReference
    true refl
    false refl

data SameObjectExperimentalLinkagePaid : Set where

noSameObjectLinkageFromRegistryTag :
  SameObjectExperimentalLinkagePaid → ⊥
noSameObjectLinkageFromRegistryTag ()

------------------------------------------------------------------------
-- Explicit outstanding external object receipts.
-- The existence of source DOI and supplementary locator is not a
-- downloaded, hashed binary nor an independent analysis.
------------------------------------------------------------------------

record UnresolvedSourceObjects : Set where
  constructor unresolvedSourceObjects
  field
    articleIdentifier : String
    articleVersionOfRecord : String
    supplementaryDataLocator : String

    originalWorkbookDigestVerified : Bool
    originalWorkbookDigestVerifiedIsFalse :
      originalWorkbookDigestVerified ≡ false

    originalSupplementDigestVerified : Bool
    originalSupplementDigestVerifiedIsFalse :
      originalSupplementDigestVerified ≡ false

paperUnresolvedSourceObjects : UnresolvedSourceObjects
paperUnresolvedSourceObjects =
  unresolvedSourceObjects
    "10.1038/s41467-022-28386-6"
    "2022-02-07"
    "Nature Communications article source data / supplementary information"
    false refl
    false refl


------------------------------------------------------------------------
-- INDEPENDENT REGISTRY-DESCRIPTOR OBSERVATIONS, NOT A SAME-OBJECT PROOF.
--
-- PubChem CID 6717 publicly displays InChIKey
-- ZAGRKAFMISFKIO-QMTHXVAHSA-N. IUPHAR/BPS Guide to Pharmacology
-- ligand 139 displays ZAGRKAFMISFKIO-IAPIXIRKSA-N while referencing
-- PubChem 6717 and CHEBI:6604. Do not guess what accounts for this
-- stereochemical-key difference, nor equate it to different experimental
-- specimens without a reviewed, version-bound chemical-structure comparison.
------------------------------------------------------------------------

iupharLysergicAcidLigand : Source.AttributedSource
iupharLysergicAcidLigand =
  Source.mkNoDOISource
    "IUPHAR/BPS Guide to PHARMACOLOGY"
    "Lysergic acid ligand 139"
    "IUPHAR/BPS Guide to PHARMACOLOGY ligand record 139"
    "current online registry record"
    "https://www.guidetopharmacology.org/GRAC/LigandDisplayForward?ligandId=139"
    Source.institutionalSource
    "Registry lists PubChem CID 6717 and ChEBI:6604 but displays a stereochemical InChIKey suffix that does not match the current PubChem-rendered suffix; the source difference requires review, not an automatic identity judgement."
    Source.publicAttribution

record RegistryDescriptorReviewResidual : Set where
  constructor registryDescriptorReviewResidual
  field
    pubChemSource : Source.AttributedSource
    iupharSource : Source.AttributedSource
    pubChemInchiKeyAsDisplayed : String
    iupharInchiKeyAsDisplayed : String
    interpretation : String

    normalisedStereochemicalMatchPaid : Bool
    normalisedStereochemicalMatchPaidIsFalse :
      normalisedStereochemicalMatchPaid ≡ false

    experimentalSampleSameObjectPaid : Bool
    experimentalSampleSameObjectPaidIsFalse :
      experimentalSampleSameObjectPaid ≡ false

registryDescriptorReview : RegistryDescriptorReviewResidual
registryDescriptorReview =
  registryDescriptorReviewResidual
    Wong.pubChemLysergicAcid
    iupharLysergicAcidLigand
    "ZAGRKAFMISFKIO-QMTHXVAHSA-N"
    "ZAGRKAFMISFKIO-IAPIXIRKSA-N"
    "A source-observed descriptor disagreement; neither a resolved stereochemical conflict nor proof that the paper's sample has a different identity."
    false refl
    false refl

paperImportNotIndependentVerification :
  DataReceiptState
paperImportNotIndependentVerification = supplementaryDataNotInspected
