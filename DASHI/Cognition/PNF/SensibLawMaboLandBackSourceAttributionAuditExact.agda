module DASHI.Cognition.PNF.SensibLawMaboLandBackSourceAttributionAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawIndigenousLandBackSourceAuthorityExact as Source
import DASHI.Cognition.PNF.SensibLawMaboPrimaryTextParserBatchMaterialisedExact as MaboBatch
import DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityParserBatchV02Exact as AuthorityBatch
import DASHI.Cognition.PNF.SensibLawCalderAuthoritativeTranscriptionVerificationExact as CalderVerify
import DASHI.Cognition.PNF.SensibLawMaboDawsonRadicalTitleRecognitionHingeExact as Hinge

------------------------------------------------------------------------
-- Audit owner for this PR tranche.
--
-- The source-attribution rules are longstanding repository rules.  This file
-- records whether the current Mabo/LAND BACK owners comply with them and where
-- an earlier local classification required correction.
------------------------------------------------------------------------

data AuditDisposition : Set where
  attributionBoundaryConfirmed : AuditDisposition
  localClassificationCorrected : AuditDisposition
  interpretiveBridgeRemainsExplicit : AuditDisposition
  unresolvedSourcePromotionBlocked : AuditDisposition


data AuditIssueKind : Set where
  parserAuthorityBoundary : AuditIssueKind
  ocrTranscriptionBoundary : AuditIssueKind
  sourceAuthorshipBoundary : AuditIssueKind
  underlyingDataProvenanceBoundary : AuditIssueKind
  publicationStatusBoundary : AuditIssueKind
  causalDesignBoundary : AuditIssueKind
  legalAuthorityBoundary : AuditIssueKind
  interpretationBoundary : AuditIssueKind
  quantitativeComparabilityBoundary : AuditIssueKind


record SourceAttributionAuditItem : Set where
  constructor sourceAttributionAuditItem
  field
    itemReference : String
    issueKind : AuditIssueKind
    disposition : AuditDisposition
    sourceOwner : String
    auditedConclusion : String
    sourceTruthPromotedByAudit : Bool
    sourceTruthPromotedByAuditIsFalse : sourceTruthPromotedByAudit ≡ false
open SourceAttributionAuditItem public

maboParserAudit : SourceAttributionAuditItem
maboParserAudit = sourceAttributionAuditItem
  "audit:mabo-parser-v01"
  parserAuthorityBoundary
  attributionBoundaryConfirmed
  "SensibLawMaboPrimaryTextParserBatchMaterialisedExact"
  "parser specimens remain candidate-only; parser does not authorize truth, occurrence or judicial holding"
  false refl

authorityParserAudit : SourceAttributionAuditItem
authorityParserAudit = sourceAttributionAuditItem
  "audit:primary-authority-parser-v02"
  parserAuthorityBoundary
  attributionBoundaryConfirmed
  "SensibLawMaboPrimaryAuthorityParserBatchV02Exact"
  "primary-authority parser observations remain candidate-only and do not themselves create reviewed legal propositions"
  false refl

calderOcrAudit : SourceAttributionAuditItem
calderOcrAudit = sourceAttributionAuditItem
  "audit:calder-ocr-authoritative-overlay"
  ocrTranscriptionBoundary
  attributionBoundaryConfirmed
  "SensibLawCalderAuthoritativeTranscriptionVerificationExact"
  "historical Calder parser text remains OCR-derived while separate SCC transcription verification supplies later source-quality promotion; provenance is not rewritten"
  false refl

cpiAuthorshipCorrection : SourceAttributionAuditItem
cpiAuthorshipCorrection = sourceAttributionAuditItem
  "audit:cpi-pucrio-authorship"
  sourceAuthorshipBoundary
  localClassificationCorrected
  "SensibLawIndigenousLandBackSourceAuthorityExact"
  "CPI/PUC-Rio analysis corrected from officialPolicyStudy to independentPolicyResearch; official SICOR/PRODES/SICAR inputs do not transfer government authorship to CPI's derived analysis"
  false refl

ashAuthorshipCorrection : SourceAttributionAuditItem
ashAuthorshipCorrection = sourceAttributionAuditItem
  "audit:ash-center-databook"
  sourceAuthorshipBoundary
  localClassificationCorrected
  "SensibLawIndigenousLandBackSourceAuthorityExact"
  "Harvard Ash Center databook is typed academicDescriptiveStatisticalSynthesis using Census/ACS data, not officialAdministrativeReceipt"
  false refl

workingPaperAudit : SourceAttributionAuditItem
workingPaperAudit = sourceAttributionAuditItem
  "audit:arcoite-johnson-working-paper"
  publicationStatusBoundary
  attributionBoundaryConfirmed
  "SensibLawIndigenousLandBackSourceAuthorityExact"
  "Arcoite & Johnson remains workingPaperCausalClaim / workingPaperNotPeerReviewed; causal-method claims are source-attributed and not promoted to peer-reviewed closure"
  false refl

wriAudit : SourceAttributionAuditItem
wriAudit = sourceAttributionAuditItem
  "audit:wri-valuation"
  causalDesignBoundary
  attributionBoundaryConfirmed
  "SensibLawIndigenousLandBackSourceAuthorityExact"
  "WRI tenure/carbon values remain economicValuationReport evidence and are not promoted to causal land-return effects or realised community revenue"
  false refl

biaAudit : SourceAttributionAuditItem
biaAudit = sourceAttributionAuditItem
  "audit:bia-carbon-policy"
  legalAuthorityBoundary
  attributionBoundaryConfirmed
  "SensibLawIndigenousLandBackSourceAuthorityExact"
  "BIA carbon-is-not-trust-asset proposition is an official administrative-policy interpretation; it does not exhaust ecological, market, cultural or Indigenous stewardship value"
  false refl

abatableAudit : SourceAttributionAuditItem
abatableAudit = sourceAttributionAuditItem
  "audit:abatable-market-price"
  publicationStatusBoundary
  attributionBoundaryConfirmed
  "SensibLawIndigenousLandBackSourceAuthorityExact"
  "Abatable REDD+ price is typed commercialMarketObservation, not social valuation, government price or causal result"
  false refl

vascoAudit : SourceAttributionAuditItem
vascoAudit = sourceAttributionAuditItem
  "audit:vasco-2018"
  causalDesignBoundary
  attributionBoundaryConfirmed
  "SensibLawIndigenousLandBackSourceAuthorityExact"
  "Vasco et al. is peerReviewedComparativeStudy; authors' explicit warning that cross-sectional estimates are not causal is preserved"
  false refl

dawsonHingeAudit : SourceAttributionAuditItem
dawsonHingeAudit = sourceAttributionAuditItem
  "audit:dawson-radical-title-recognition-hinge"
  interpretationBoundary
  interpretiveBridgeRemainsExplicit
  "SensibLawMaboDawsonRadicalTitleRecognitionHingeExact"
  "direct primary Dawson text supports recognition-inference/acquiescence evidence; radical-title-to-constitutive-recognition bridge remains unresolved doctrinal inference rather than primary holding"
  false refl

allCurrentAuditItems : List SourceAttributionAuditItem
allCurrentAuditItems =
  maboParserAudit
  ∷ authorityParserAudit
  ∷ calderOcrAudit
  ∷ cpiAuthorshipCorrection
  ∷ ashAuthorshipCorrection
  ∷ workingPaperAudit
  ∷ wriAudit
  ∷ biaAudit
  ∷ abatableAudit
  ∷ vascoAudit
  ∷ dawsonHingeAudit
  ∷ []

------------------------------------------------------------------------
-- Mechanical cross-checks against source owners.
------------------------------------------------------------------------

cpiNowIndependentPolicyResearch :
  Source.authorityKind Source.cpi2024RuralCreditAuthority ≡ Source.independentPolicyResearch
cpiNowIndependentPolicyResearch = refl

cpiUsesOfficialInputsWithoutGovernmentAuthorship :
  Source.usesOfficialUnderlyingData Source.cpi2024RuralCreditAuthority ≡ true
cpiUsesOfficialInputsWithoutGovernmentAuthorship = refl

cpiAnalysisAuthorNotGovernment :
  Source.analysisAuthorIsGovernment Source.cpi2024RuralCreditAuthority ≡ false
cpiAnalysisAuthorNotGovernment = refl

ashNowAcademicSynthesis :
  Source.authorityKind Source.ashCenter2025DatabookAuthority ≡ Source.academicDescriptiveStatisticalSynthesis
ashNowAcademicSynthesis = refl

arcoiteStillWorkingPaper :
  Source.publicationStatus Source.arcoiteJohnson2025Authority ≡ Source.workingPaperNotPeerReviewed
arcoiteStillWorkingPaper = refl

biaStillAdministrativePolicy :
  Source.authorityKind Source.biaCarbon2023Authority ≡ Source.officialAdministrativePolicy
biaStillAdministrativePolicy = refl

abatableStillCommercialObservation :
  Source.authorityKind Source.abatable2025ReddPriceAuthority ≡ Source.commercialMarketObservation
abatableStillCommercialObservation = refl

dawsonHingeStillUnresolved :
  Hinge.sourceStatus Hinge.radicalTitleRecognitionMediationCandidate ≡ Hinge.unresolvedBridge
dawsonHingeStillUnresolved = refl

------------------------------------------------------------------------
-- Standing no-transfer rules.
------------------------------------------------------------------------

data AuditCreatesSourceTruth : Set where
data OfficialInputTransfersDerivedAuthorship : Set where
data SourceClassificationDeterminesWorldTruth : Set where
data CorrectCitationMakesInterpretiveBridgePrimaryText : Set where

auditDoesNotCreateTruth : AuditCreatesSourceTruth → ⊥
auditDoesNotCreateTruth ()
officialInputDoesNotTransferDerivedAuthorship : OfficialInputTransfersDerivedAuthorship → ⊥
officialInputDoesNotTransferDerivedAuthorship ()
classificationDoesNotDetermineWorldTruth : SourceClassificationDeterminesWorldTruth → ⊥
classificationDoesNotDetermineWorldTruth ()
citationDoesNotPromoteInterpretationToPrimary : CorrectCitationMakesInterpretiveBridgePrimaryText → ⊥
citationDoesNotPromoteInterpretationToPrimary ()
