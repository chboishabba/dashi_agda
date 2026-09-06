module DASHI.Cognition.PNF.SensibLawMaboRecognitionBasisAuthorityEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboBrennanDawsonIssueResidualLiveExact as Mabo

------------------------------------------------------------------------
-- AUTHORITY-USE RECEIPTS FOR THE LIVE MABO RECOGNITION-BASIS RESIDUAL.
--
-- Source discipline:
--   * a citation occurrence is not adoption;
--   * a later doctrinal source is not silently promoted to judgment text;
--   * the same authority may be used differently by different judges;
--   * authority-use classification is a reviewed receipt, not a spaCy output.
------------------------------------------------------------------------

data SourceTier : Set where
  primaryJudgmentReproduction
  officialInstitutionalSummary
  secondaryDoctrinalAnalysis
  : SourceTier

data AuthorityUseKind : Set where
  continuityRuleUse
  recognitionDoctrineUse
  radicalTitleCompatibilityUse
  evidentialRecognitionUse
  contraryRuleUse
  authorityInterpretationUse
  : AuthorityUseKind

data CitationRelation : Set where
  citedSupportively
  citedAsContrary
  citedAndQualified
  citedToExplain
  : CitationRelation

record LegalAuthorityIdentity : Set where
  constructor legalAuthorityIdentity
  field
    authorityReference : String
    canonicalCitation : String
open LegalAuthorityIdentity public

reSouthernRhodesia : LegalAuthorityIdentity
reSouthernRhodesia = legalAuthorityIdentity
  "authority:Re-Southern-Rhodesia-1919"
  "In re Southern Rhodesia [1919] AC 211"

amoduTijani : LegalAuthorityIdentity
amoduTijani = legalAuthorityIdentity
  "authority:Amodu-Tijani-1921"
  "Amodu Tijani v Secretary, Southern Nigeria [1921] 2 AC 399"

oyekan : LegalAuthorityIdentity
oyekan = legalAuthorityIdentity
  "authority:Oyekan-v-Adele-1957"
  "Oyekan v Adele [1957] 1 WLR 876"

sobhuza : LegalAuthorityIdentity
sobhuza = legalAuthorityIdentity
  "authority:Sobhuza-II-v-Miller-1926"
  "Sobhuza II v Miller [1926] AC 518"

calder : LegalAuthorityIdentity
calder = legalAuthorityIdentity
  "authority:Calder-v-AG-BC-1973"
  "Calder v Attorney-General of British Columbia [1973] SCR 313"

record AuthorityUseReceipt
    (proposition : Mabo.ReviewedJudicialProposition) : Set where
  constructor authorityUseReceipt
  field
    authority : LegalAuthorityIdentity
    useKind : AuthorityUseKind
    citationRelation : CitationRelation
    judgmentPinpoint : String
    sourceTier : SourceTier
    sourceReference : String
    reviewedUseClassification : Bool
    reviewedUseClassificationIsTrue : reviewedUseClassification ≡ true
    citationAloneMeansAdoption : Bool
    citationAloneMeansAdoptionIsFalse : citationAloneMeansAdoption ≡ false
    secondarySourceReplacesPrimaryJudgment : Bool
    secondarySourceReplacesPrimaryJudgmentIsFalse : secondarySourceReplacesPrimaryJudgment ≡ false
open AuthorityUseReceipt public

------------------------------------------------------------------------
-- Brennan: continuity / survival route.
------------------------------------------------------------------------

brennanSouthernRhodesiaUse : AuthorityUseReceipt Mabo.brennanSurvivalProposition
brennanSouthernRhodesiaUse = authorityUseReceipt
  reSouthernRhodesia continuityRuleUse citedSupportively
  "Mabo (No 2) 175 CLR 1 at 55-57; para 61 summary of preferable rule"
  primaryJudgmentReproduction
  "primary judgment reproduction: Brennan J states preferable rule that mere change in sovereignty does not extinguish native title and invokes In re Southern Rhodesia"
  true refl false refl false refl

brennanAmoduUse : AuthorityUseReceipt Mabo.brennanSurvivalProposition
brennanAmoduUse = authorityUseReceipt
  amoduTijani radicalTitleCompatibilityUse citedSupportively
  "Mabo (No 2) 175 CLR 1 around 40-41 and 55-57"
  primaryJudgmentReproduction
  "primary judgment reproduction: Amodu Tijani used for native title capable of burdening/qualifying radical title and continuity reasoning"
  true refl false refl false refl

brennanOyekanUse : AuthorityUseReceipt Mabo.brennanSurvivalProposition
brennanOyekanUse = authorityUseReceipt
  oyekan continuityRuleUse citedSupportively
  "Mabo (No 2) 175 CLR 1 at 55-56"
  secondaryDoctrinalAnalysis
  "doctrinal recovery cross-check: Brennan J cites Oyekan in the continuity/presumption line; primary pinpoint retained as target for direct-source verification"
  true refl false refl false refl

brennanCalderUse : AuthorityUseReceipt Mabo.brennanSurvivalProposition
brennanCalderUse = authorityUseReceipt
  calder continuityRuleUse citedSupportively
  "Mabo (No 2) 175 CLR 1 para 60-61"
  primaryJudgmentReproduction
  "primary judgment reproduction: Hall J in Calder cited against proposition that native peoples have only rights subsequently granted or recognised"
  true refl false refl false refl

------------------------------------------------------------------------
-- Dawson: Crown-recognition / acquiescence route.
------------------------------------------------------------------------

dawsonAmoduUse : AuthorityUseReceipt Mabo.dawsonRecognitionProposition
dawsonAmoduUse = authorityUseReceipt
  amoduTijani recognitionDoctrineUse citedSupportively
  "Dawson J para 8, Amodu Tijani at 407"
  primaryJudgmentReproduction
  "primary judgment reproduction: authority used in discussion of whether a new sovereign recognises or accepts pre-existing rights"
  true refl false refl false refl

dawsonCalderUse : AuthorityUseReceipt Mabo.dawsonRecognitionProposition
dawsonCalderUse = authorityUseReceipt
  calder authorityInterpretationUse citedAndQualified
  "Dawson J paras 13-16"
  primaryJudgmentReproduction
  "primary judgment reproduction: Dawson explains Calder as consistent with recognition by Crown including acquiescence, and rejects an interpretation of survival wholly independent of Crown recognition"
  true refl false refl false refl

------------------------------------------------------------------------
-- Same-authority divergent-use seam.
------------------------------------------------------------------------

record SharedAuthorityUseContrast
    {left right : Mabo.ReviewedJudicialProposition}
    (leftUse : AuthorityUseReceipt left)
    (rightUse : AuthorityUseReceipt right) : Set where
  constructor sharedAuthorityUseContrast
  field
    sameAuthority : authorityReference (authority leftUse) ≡ authorityReference (authority rightUse)
    useKindsDiffer : Bool
    useKindsDifferIsTrue : useKindsDiffer ≡ true
    reviewedContrastReference : String
open SharedAuthorityUseContrast public

amoduUseContrast : SharedAuthorityUseContrast brennanAmoduUse dawsonAmoduUse
amoduUseContrast = sharedAuthorityUseContrast refl true refl
  "same Amodu Tijani authority; Brennan use classified toward radical-title compatibility/continuity while Dawson use is classified in Crown-recognition analysis"

calderUseContrast : SharedAuthorityUseContrast brennanCalderUse dawsonCalderUse
calderUseContrast = sharedAuthorityUseContrast refl true refl
  "same Calder authority; Brennan uses Hall J against grant/recognition-dependence while Dawson later qualifies Calder through Crown recognition including acquiescence"

------------------------------------------------------------------------
-- Hard source-attribution boundaries.
------------------------------------------------------------------------

data CitationMeansAdoption : Set where
data SharedAuthorityMeansSharedLegalRole : Set where
data SecondaryAnalysisIsPrimaryJudgment : Set where
data SameCitationMeansSameProposition : Set where

aCitationDoesNotMeanAdoption : CitationMeansAdoption → ⊥
aCitationDoesNotMeanAdoption ()
sharedAuthorityDoesNotForceSharedRole : SharedAuthorityMeansSharedLegalRole → ⊥
sharedAuthorityDoesNotForceSharedRole ()
secondaryAnalysisDoesNotBecomePrimary : SecondaryAnalysisIsPrimaryJudgment → ⊥
secondaryAnalysisDoesNotBecomePrimary ()
sameCitationDoesNotForceSameProposition : SameCitationMeansSameProposition → ⊥
sameCitationDoesNotForceSameProposition ()
