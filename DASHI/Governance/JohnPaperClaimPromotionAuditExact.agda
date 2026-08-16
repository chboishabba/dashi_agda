module DASHI.Governance.JohnPaperClaimPromotionAuditExact where

------------------------------------------------------------------------
-- USER-SUPPLIED DRAFT SOURCE
--
-- File: "Johns-Research-Paper_3_tracked changes.docx".
-- Persistent/cloud draft supplied by the user; no DOI asserted for the draft.
--
-- Relevant draft surfaces used by this audit include:
--   * safety/autonomy/psychological-development concerns around the childhood
--     religious "introduction process";
--   * comparison of coercive religious practices with traumatic experiences;
--   * recommendations for regulation and legal reform;
--   * an especially high-risk list naming modern-day slavery, entrapment,
--     psychological/physical battery, fraud, tax evasion and deception.
--
-- This file formalizes the CLAIM PROMOTION GRAPH only.  A draft sentence is a
-- claim occurrence, not an empirical, causal, normative, diagnostic or legal
-- receipt.  Legal categories require jurisdiction-specific external authority.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.DevelopmentalInfluenceSourceAtlas as Sources
import DASHI.Governance.RepresentationCarrierVerificationCore as Verification

------------------------------------------------------------------------
-- Claim layers.
------------------------------------------------------------------------

data ClaimLayer : Set where
  descriptiveLayer empiricalLayer mechanismLayer normativeLayer legalLayer : ClaimLayer

record PaperClaim : Set where
  constructor paperClaim
  field
    label : String
    layer : ClaimLayer
    draftLocator : String

open PaperClaim public

developmentalInfluenceClaim : PaperClaim
developmentalInfluenceClaim =
  paperClaim
    "childhood religious introduction may affect autonomy / psychological development"
    empiricalLayer
    "draft safety/ethics section: potential risks associated with coercion, loss of autonomy and psychological development"

indoctrinationClassificationClaim : PaperClaim
indoctrinationClassificationClaim =
  paperClaim
    "the relevant childhood influence qualifies as religious indoctrination"
    mechanismLayer
    "draft repeatedly uses religious indoctrination / coercive religious-practice language"

traumaSimilarityClaim : PaperClaim
traumaSimilarityClaim =
  paperClaim
    "religious indoctrination has similarities to traumatic experiences"
    mechanismLayer
    "draft comparison/discussion and future-research sections"

regulationRecommendationClaim : PaperClaim
regulationRecommendationClaim =
  paperClaim
    "coercive religious practices should be regulated / subject to legal reform"
    normativeLayer
    "draft policy/legal-measures sections"

fraudLegalClaim : PaperClaim
fraudLegalClaim =
  paperClaim
    "the relevant conduct satisfies legal fraud"
    legalLayer
    "draft high-risk legal-category list includes fraud"

batteryLegalClaim : PaperClaim
batteryLegalClaim =
  paperClaim
    "the relevant conduct satisfies psychological or physical battery"
    legalLayer
    "draft high-risk legal-category list includes psychological and physical battery"

modernSlaveryLegalClaim : PaperClaim
modernSlaveryLegalClaim =
  paperClaim
    "the relevant conduct satisfies modern-day slavery"
    legalLayer
    "draft high-risk legal-category list includes modern-day slavery"

------------------------------------------------------------------------
-- Typed receipts.  Each promotion edge has a distinct proof object.
------------------------------------------------------------------------

record EmpiricalReceipt (claim : PaperClaim) : Set₁ where
  constructor empiricalReceipt
  field
    sources : List Sources.ScholarlySource
    Evidence : Set
    evidence : Evidence
    scope : String

record MechanismReceipt (from to : PaperClaim) : Set₁ where
  constructor mechanismReceipt
  field
    sources : List Sources.ScholarlySource
    MechanismEvidence : Set
    mechanismEvidence : MechanismEvidence
    scope : String

record NormativeReceipt (from to : PaperClaim) : Set₁ where
  constructor normativeReceipt
  field
    NormativePremise : Set
    normativePremise : NormativePremise
    publicReasonScope : String

record ExternalLegalReceipt (from to : PaperClaim) : Set₁ where
  constructor externalLegalReceipt
  field
    jurisdiction : String
    authority : String
    LegalElements : Set
    legalElements : LegalElements
    factToElementMapping : String

------------------------------------------------------------------------
-- Claim graph edges are only constructible with the corresponding receipt.
------------------------------------------------------------------------

record EmpiricalToMechanismEdge (from to : PaperClaim) : Set₁ where
  constructor empiricalToMechanismEdge
  field receipt : MechanismReceipt from to

record MechanismToNormativeEdge (from to : PaperClaim) : Set₁ where
  constructor mechanismToNormativeEdge
  field receipt : NormativeReceipt from to

record NormativeToLegalEdge (from to : PaperClaim) : Set₁ where
  constructor normativeToLegalEdge
  field receipt : ExternalLegalReceipt from to

------------------------------------------------------------------------
-- Bounded scholarly counter-position installed now.
--
-- Hanks is used as a philosophical boundary: asymmetrical initiation into a
-- space of reasons need not itself establish autonomy-destroying
-- indoctrination.  This does not settle the empirical Catholic-practice case.
------------------------------------------------------------------------

hanksCounterPosition : Sources.ScholarlySource
hanksCounterPosition = Sources.indoctrinationSpaceReasons

record DevelopmentalInfluenceToIndoctrinationBoundary : Set where
  constructor developmentalInfluenceToIndoctrinationBoundary
  field
    earlyAsymmetryAloneEstablishesIndoctrination : Bool
    developmentalInfluenceNeedsAdditionalMechanismEvidence : Bool
    adultEndorsementAloneSettlesFormationAutonomy : Bool

canonicalDevelopmentalInfluenceToIndoctrinationBoundary :
  DevelopmentalInfluenceToIndoctrinationBoundary
canonicalDevelopmentalInfluenceToIndoctrinationBoundary =
  developmentalInfluenceToIndoctrinationBoundary false true false

------------------------------------------------------------------------
-- Fail-closed legal promotion for the three strongest draft labels.
--
-- The module intentionally installs NO jurisdiction-specific ExternalLegalReceipt
-- for fraud, battery or modern slavery.  The point is not to prove those labels
-- false; it is to prevent the draft text or a developmental mechanism claim
-- from silently inhabiting the legal conclusion.
------------------------------------------------------------------------

record JohnPaperPromotionAudit : Set where
  constructor johnPaperPromotionAudit
  field
    draftTextIsEvidenceReceipt : Bool
    developmentalInfluenceAutomaticallyEqualsIndoctrination : Bool
    traumaSimilarityAutomaticallyEqualsClinicalTrauma : Bool
    normativeConcernAutomaticallyCreatesLegalClassification : Bool
    fraudExternalLegalReceiptInstalled : Bool
    batteryExternalLegalReceiptInstalled : Bool
    modernSlaveryExternalLegalReceiptInstalled : Bool
    legalPromotionRequiresJurisdictionSpecificReceipt : Bool
    paperReferencesDeclaredVerifiedByThisModule : Bool

canonicalJohnPaperPromotionAudit : JohnPaperPromotionAudit
canonicalJohnPaperPromotionAudit =
  johnPaperPromotionAudit
    false false false false false false false true false

------------------------------------------------------------------------
-- Cross-check with the existing representation/carrier promotion discipline.
------------------------------------------------------------------------

existingVerificationBoundaryAgrees :
  Verification.RepresentationCarrierReceipt.normativeClassificationSeparatedFromLegalConclusion
    Verification.canonicalRepresentationCarrierReceipt
  ≡ true
existingVerificationBoundaryAgrees = refl

------------------------------------------------------------------------
-- Explicit missing-edge tokens used by regression.  They describe what is NOT
-- constructed in this tranche; they are not claims that such evidence could
-- never exist.
------------------------------------------------------------------------

data DraftTextPromotesFraudWithoutLegalReceipt : Set where

data DraftTextPromotesBatteryWithoutLegalReceipt : Set where

data DraftTextPromotesModernSlaveryWithoutLegalReceipt : Set where

draftTextDoesNotPromoteFraudWithoutLegalReceipt :
  DraftTextPromotesFraudWithoutLegalReceipt → ⊥
draftTextDoesNotPromoteFraudWithoutLegalReceipt ()

draftTextDoesNotPromoteBatteryWithoutLegalReceipt :
  DraftTextPromotesBatteryWithoutLegalReceipt → ⊥
draftTextDoesNotPromoteBatteryWithoutLegalReceipt ()

draftTextDoesNotPromoteModernSlaveryWithoutLegalReceipt :
  DraftTextPromotesModernSlaveryWithoutLegalReceipt → ⊥
draftTextDoesNotPromoteModernSlaveryWithoutLegalReceipt ()
