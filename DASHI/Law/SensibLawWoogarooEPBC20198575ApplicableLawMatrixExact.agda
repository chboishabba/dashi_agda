module DASHI.Law.SensibLawWoogarooEPBC20198575ApplicableLawMatrixExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- EPBC 2019/8575 APPLICABLE-LAW MATRIX
--
-- Provision-by-provision transition audit for the pending Part 9 decision.
-- Source basis: Environment Protection Reform Act 2025, Schedule 1 Part 3,
-- especially items 683, 689 and 690, plus the August 2026 transitional rules.
-- This is a source-bounded reconstruction for counsel review, not legal advice.
------------------------------------------------------------------------

data RuleBucket : Set where
  preReformPreserved : RuleBucket
  postReformApplies : RuleBucket
  mixedOrProvisionSpecific : RuleBucket
  counselConstructionOpen : RuleBucket

record ApplicableRule : Set where
  constructor applicable-rule
  field
    provision : String
    transitionSource : String
    bucket : RuleBucket
    boundedEffect : String
    automaticMeritsConclusion : Bool

open ApplicableRule public

assessmentDivision4 : ApplicableRule
assessmentDivision4 = applicable-rule
  "EPBC Part 8 Division 4 — assessment on preliminary documentation"
  "Environment Protection Reform Act 2025 Sch 1 Pt 3 item 683(1)(a)"
  preReformPreserved
  "Because the s 87 assessment approach for EPBC 2019/8575 was chosen before 24 August 2026, the specified amendments to Division 4 do not apply to this action."
  false

section130_1B : ApplicableRule
section130_1B = applicable-rule
  "EPBC s 130(1B)"
  "Environment Protection Reform Act 2025 Sch 1 Pt 3 item 683(1)(f)"
  preReformPreserved
  "The specified amendment to s 130(1B) does not apply where the s 87 assessment approach was chosen before commencement."
  false

section135AAssessmentChange : ApplicableRule
section135AAssessmentChange = applicable-rule
  "EPBC s 135A — assessment-pathway amendment"
  "Environment Protection Reform Act 2025 Sch 1 Pt 3 item 683(1)(i)"
  preReformPreserved
  "The specified s 135A amendments captured by item 683 do not apply to this pre-commencement s 87 assessment approach."
  false

section135APublication : ApplicableRule
section135APublication = applicable-rule
  "EPBC s 135A(2)-(4) — publication of recommendation reports"
  "Environment Protection Reform Act 2025 Sch 1 Pt 3 item 689"
  postReformApplies
  "The publication amendments apply to a recommendation report given to the Minister on or after 24 August 2026, even if the report was prepared before commencement."
  false

section136Paragraphs : ApplicableRule
section136Paragraphs = applicable-rule
  "EPBC s 136(2)(ba)/(c)/(bd) assessment-linked amendments"
  "Environment Protection Reform Act 2025 Sch 1 Pt 3 item 683(1)(j)"
  preReformPreserved
  "The repeal/insertion specified in item 683(1)(j) does not apply to this action because its s 87 assessment approach predates commencement."
  false

newPart9Sections138139 : ApplicableRule
newPart9Sections138139 = applicable-rule
  "EPBC ss 138 and 139 as substituted by the 2025 Reform Act"
  "Environment Protection Reform Act 2025 Sch 1 Pt 3 item 690(1)(g)"
  preReformPreserved
  "The substituted ss 138 and 139 apply only where the relevant referral was made on or after 24 August 2026. EPBC 2019/8575 predates that date, so those substituted provisions do not apply to this referral."
  false

newPart9Sections136ABC : ApplicableRule
newPart9Sections136ABC = applicable-rule
  "EPBC ss 136A, 136B and 136C inserted by the 2025 Reform Act"
  "Environment Protection Reform Act 2025 Sch 1 Pt 3 item 690(1)(d)-(f)"
  preReformPreserved
  "These new approval-consideration provisions apply only to referrals made on or after 24 August 2026 and therefore do not automatically govern EPBC 2019/8575."
  false

newSection134Changes : ApplicableRule
newSection134Changes = applicable-rule
  "specified 2025 Reform Act amendments to EPBC s 134"
  "Environment Protection Reform Act 2025 Sch 1 Pt 3 item 690(1)(a)-(c)"
  preReformPreserved
  "The specified new s 134 amendments are tied by item 690(1) to referrals made on or after commencement; the pre-reform s 134 framework remains the relevant starting point for 2019/8575, subject to any other transition provision."
  false

postApproval143to145 : ApplicableRule
postApproval143to145 = applicable-rule
  "EPBC ss 143(2B), 144(2B)-(2C), 145(2C)-(2D), 145B(3A), 145D(3B)"
  "Environment Protection Reform Act 2025 Sch 1 Pt 3 item 690(2)"
  postReformApplies
  "These inserted provisions apply to Part 9 decisions made on or after commencement whether the underlying referral occurred before, on or after commencement."
  false

section145AA : ApplicableRule
section145AA = applicable-rule
  "EPBC s 145AA"
  "Environment Protection Reform Act 2025 Sch 1 Pt 3 item 690(3)"
  postReformApplies
  "Section 145AA applies to approvals whether the approval was given before, on or after commencement."
  false

requestsForInformation : ApplicableRule
requestsForInformation = applicable-rule
  "EPBC ss 76, 89 and 132 request-for-information amendments"
  "Environment Protection Reform Act 2025 Sch 1 Pt 3 item 686"
  postReformApplies
  "The specified amendments apply to decisions the Minister is to make whether the action was referred before, on or after commencement."
  false

record ApplicableLawSummary : Set where
  constructor applicable-law-summary
  field
    referralPredates24Aug2026 : Bool
    assessmentApproachPredates24Aug2026 : Bool
    oldDivision4FrameworkPreserved : Bool
    substitutedSections138139Apply : Bool
    new136ABCApply : Bool
    somePostCommencementRulesStillApply : Bool
    currentConsolidatedActAloneSufficient : Bool
    counselReviewRequired : Bool

current20198575ApplicableLaw : ApplicableLawSummary
current20198575ApplicableLaw = applicable-law-summary
  true
  true
  true
  false
  false
  true
  false
  true

------------------------------------------------------------------------
-- WrongType / transition boundaries.
------------------------------------------------------------------------

record ApplicableLawBoundary : Set where
  constructor applicable-law-boundary
  field
    currentSectionNumberDoesNotImplyCurrentTextApplies : Bool
    preCommencementReferralDoesNotFreezeWholeAct : Bool
    oneTransitionItemDoesNotDetermineEveryProvision : Bool
    transitionStatusDoesNotDetermineMerits : Bool
    newProtectiveRuleNotApplicableDoesNotProveApproval : Bool

applicableLawBoundary : ApplicableLawBoundary
applicableLawBoundary = applicable-law-boundary true true true true true

record CounselResidual : Set where
  constructor counsel-residual
  field
    question : String
    status : String

remainingCounselResidual : CounselResidual
remainingCounselResidual = counsel-residual
  "Confirm the exact text/version of each operative pre-reform provision governing EPBC 2019/8575 at the 1 October 2026 decision, and identify any later transitional rule, instrument, court authority or commencement item that modifies the item-683/item-690 mapping."
  "Provision buckets are source-mapped; final legal construction remains counsel-owned."
