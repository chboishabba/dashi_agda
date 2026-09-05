module DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityUseUpgradeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboRecognitionBasisAuthorityEvidenceExact as Use
import DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityPropositionWeldExact as Primary
import DASHI.Cognition.PNF.SensibLawMaboRecognitionCoordinateFactorisationExact as Factor

------------------------------------------------------------------------
-- Relation between a Mabo authority-use receipt and a proposition recovered
-- from the cited authority's own primary text.
--
-- This is deliberately not equality.  A later judge may support, qualify,
-- contrast with, or leave unresolved a proposition appearing in the cited
-- authority.  The relation itself is reviewed, not parser-produced.
------------------------------------------------------------------------

data PrimaryUseRelation : Set where
  primarySupportsLaterUse
  primaryQualifiesLaterUse
  primaryContrastsLaterUse
  primaryRelationUnresolved
  : PrimaryUseRelation

record PrimaryAuthorityUseWeld
    {maboProposition : _}
    (laterUse : Use.AuthorityUseReceipt maboProposition)
    (primary : Primary.ReviewedPrimaryAuthorityProposition) : Set where
  constructor primaryAuthorityUseWeld
  field
    sameAuthorityIdentity :
      Use.authorityReference (Use.authority laterUse) ≡
      Use.authorityReference (Primary.authorityIdentity primary)
    relation : PrimaryUseRelation
    coordinateReference : Factor.RecognitionCoordinate
    reviewedRelation : Bool
    reviewedRelationIsTrue : reviewedRelation ≡ true
    parserAloneAuthorizesRelation : Bool
    parserAloneAuthorizesRelationIsFalse : parserAloneAuthorizesRelation ≡ false
    relationReference : String
open PrimaryAuthorityUseWeld public

------------------------------------------------------------------------
-- Amodu Tijani.
------------------------------------------------------------------------

brennanAmoduRadicalTitleWeld :
  PrimaryAuthorityUseWeld Use.brennanAmoduUse Primary.amoduUsufructBurdenProposition
brennanAmoduRadicalTitleWeld = primaryAuthorityUseWeld
  refl primarySupportsLaterUse Factor.radicalTitleCompatibility
  true refl false refl
  "Amodu primary text expressly describes native usufruct as qualifying/burdening radical/final title; this supports the reviewed Brennan radical-title-compatibility use"

brennanAmoduPureEstateWeld :
  PrimaryAuthorityUseWeld Use.brennanAmoduUse Primary.amoduPureLegalEstateProposition
brennanAmoduPureEstateWeld = primaryAuthorityUseWeld
  refl primarySupportsLaterUse Factor.radicalTitleCompatibility
  true refl false refl
  "Amodu primary text distinguishes the Sovereign's pure legal estate from beneficial rights; this supports the reviewed Brennan radical-title distinction"

brennanAmoduContinuityWeld :
  PrimaryAuthorityUseWeld Use.brennanAmoduUse Primary.amoduCessionContinuityProposition
brennanAmoduContinuityWeld = primaryAuthorityUseWeld
  refl primarySupportsLaterUse Factor.continuityAcrossSovereignty
  true refl false refl
  "Amodu primary cession passage supports continuity across sovereignty but is additional to, not identical with, Brennan's radical-title authority-use classification"

dawsonAmoduContinuityWeld :
  PrimaryAuthorityUseWeld Use.dawsonAmoduUse Primary.amoduCessionContinuityProposition
dawsonAmoduContinuityWeld = primaryAuthorityUseWeld
  refl primaryQualifiesLaterUse Factor.crownRecognitionRequirement
  true refl false refl
  "Amodu primary text preserves inhabitants' rights across cession; this qualifies a broad reading that legal survival is produced only by later Crown recognition"

dawsonAmoduNoDisplacementWeld :
  PrimaryAuthorityUseWeld Use.dawsonAmoduUse Primary.amoduNoBeneficialDisplacementProposition
dawsonAmoduNoDisplacementWeld = primaryAuthorityUseWeld
  refl primaryQualifiesLaterUse Factor.crownRecognitionRequirement
  true refl false refl
  "Amodu primary text rejects beneficial-Crown-title displacement of presumptive native title; this is relevant to, but does not by itself settle, Dawson's recognition analysis"

------------------------------------------------------------------------
-- Calder.
------------------------------------------------------------------------

brennanCalderIndependentTitleWeld :
  PrimaryAuthorityUseWeld Use.brennanCalderUse Primary.hallIndependentTitleProposition
brennanCalderIndependentTitleWeld = primaryAuthorityUseWeld
  refl primarySupportsLaterUse Factor.antecedentRightExistence
  true refl false refl
  "Hall J OCR-primary proposition says aboriginal title does not depend on treaty, executive order or legislation; this supports Brennan's reviewed use against grant/recognition dependence"

brennanCalderSurvivalWeld :
  PrimaryAuthorityUseWeld Use.brennanCalderUse Primary.hallSurvivalWithoutRecognitionProposition
brennanCalderSurvivalWeld = primaryAuthorityUseWeld
  refl primarySupportsLaterUse Factor.continuityAcrossSovereignty
  true refl false refl
  "Hall J OCR-primary proposition expressly treats survival as independent of sovereign recognition; this supports Brennan's continuity-side use"

dawsonCalderRecognitionWeld :
  PrimaryAuthorityUseWeld Use.dawsonCalderUse Primary.hallRecognitionNotPrerequisiteProposition
dawsonCalderRecognitionWeld = primaryAuthorityUseWeld
  refl primaryContrastsLaterUse Factor.crownRecognitionRequirement
  true refl false refl
  "Hall J OCR-primary proposition denies affirmative governmental recognition as a prerequisite to original title; this contrasts with Dawson's later reviewed Calder interpretation through Crown recognition"

dawsonCalderSurvivalWeld :
  PrimaryAuthorityUseWeld Use.dawsonCalderUse Primary.hallSurvivalWithoutRecognitionProposition
dawsonCalderSurvivalWeld = primaryAuthorityUseWeld
  refl primaryContrastsLaterUse Factor.continuityAcrossSovereignty
  true refl false refl
  "Hall J OCR-primary proposition says survival does not depend on sovereign recognition; Dawson's Mabo treatment is therefore recorded as a reviewed interpretive contrast, not as the same proposition"

dawsonCalderJudsonWeld :
  PrimaryAuthorityUseWeld Use.dawsonCalderUse Primary.judsonRecognizedUnrecognizedProposition
dawsonCalderJudsonWeld = primaryAuthorityUseWeld
  refl primaryQualifiesLaterUse Factor.authorityInterpretation
  true refl false refl
  "Judson J OCR-primary material discusses and rejects a simple recognised/unrecognised dichotomy in the Tillamook compensation line; it informs but does not itself prove Dawson's recognition doctrine"

------------------------------------------------------------------------
-- High-value disagreement receipt.
------------------------------------------------------------------------

record SameAuthorityPrimaryInterpretiveContrast : Set where
  constructor sameAuthorityPrimaryInterpretiveContrast
  field
    authorityReference : String
    primaryPropositionReference : String
    brennanRelation : PrimaryUseRelation
    dawsonRelation : PrimaryUseRelation
    relationKindsDiffer : Bool
    relationKindsDifferIsTrue : relationKindsDiffer ≡ true
    contrastCoordinate : Factor.RecognitionCoordinate
    contrastReference : String
open SameAuthorityPrimaryInterpretiveContrast public

calderHallRecognitionContrast : SameAuthorityPrimaryInterpretiveContrast
calderHallRecognitionContrast = sameAuthorityPrimaryInterpretiveContrast
  "authority:Calder-v-AG-BC-1973"
  (Primary.propositionReference Primary.hallRecognitionNotPrerequisiteProposition)
  primarySupportsLaterUse
  primaryContrastsLaterUse
  true refl
  Factor.crownRecognitionRequirement
  "same Calder authority and Hall primary proposition: Brennan-side reviewed use aligns with recognition-independence; Dawson-side reviewed use is recorded as an interpretive contrast"

amoduContinuityInterpretiveContrast : SameAuthorityPrimaryInterpretiveContrast
amoduContinuityInterpretiveContrast = sameAuthorityPrimaryInterpretiveContrast
  "authority:Amodu-Tijani-1921"
  (Primary.propositionReference Primary.amoduCessionContinuityProposition)
  primarySupportsLaterUse
  primaryQualifiesLaterUse
  true refl
  Factor.continuityAcrossSovereignty
  "same Amodu primary continuity proposition supports Brennan's continuity/radical-title lane while qualifying a recognition-dependent reading in Dawson"

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data SameAuthorityMeansSameInterpretation : Set where
data PrimaryTextForcesLaterJudicialUse : Set where
data PrimarySupportMeansAuthorityAdoptedWithoutQualification : Set where
data PrimaryContrastMakesLaterJudgmentFalse : Set where
data OcrContrastIsAuthoritativeQuotation : Set where

sameAuthorityDoesNotMeanSameInterpretation : SameAuthorityMeansSameInterpretation → ⊥
sameAuthorityDoesNotMeanSameInterpretation ()
primaryTextDoesNotForceLaterUse : PrimaryTextForcesLaterJudicialUse → ⊥
primaryTextDoesNotForceLaterUse ()
primarySupportDoesNotEraseQualification : PrimarySupportMeansAuthorityAdoptedWithoutQualification → ⊥
primarySupportDoesNotEraseQualification ()
primaryContrastDoesNotMakeLaterJudgmentFalse : PrimaryContrastMakesLaterJudgmentFalse → ⊥
primaryContrastDoesNotMakeLaterJudgmentFalse ()
ocrContrastDoesNotBecomeAuthoritativeQuotation : OcrContrastIsAuthoritativeQuotation → ⊥
ocrContrastDoesNotBecomeAuthoritativeQuotation ()
