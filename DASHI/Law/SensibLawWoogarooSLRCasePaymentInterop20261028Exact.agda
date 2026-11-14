module DASHI.Law.SensibLawWoogarooSLRCasePaymentInterop20261028Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawWoogarooEPBC8575PleadableGroundsPrecedentCut20261028Exact as Case
import DASHI.Law.SensibLawWoogarooStandingTimeInterimCounselTriage20261027Exact as Counsel
import DASHI.Law.SensibLawWoogarooEPBC95C135ADecisionFileMaxCut20261027Exact as File
import DASHI.Law.SensibLawWoogarooEPBC8575CumulativeImpactSufficiencyExact as Cumulative
import DASHI.Law.SensibLawWoogaroo9281Condition6aEvidenceStateExact as Council

------------------------------------------------------------------------
-- WOOGAROO CROSS-REPO CASE-REF / PAYMENT BRIDGE (SOURCE-WRITTEN)
--
-- Native existing owners:
-- DASHI: Case seven-ground authority/defence/falsifier.
-- SensibLaw PR #500: src/sources/woogaroo_case_cut.py; source role,
--   identity, seven gate=0 tests, no persisted exact span.
-- SLR PR #59: MatterControversyDraft candidate-only source-scoped test;
--   only advice and local habitat residuals currently instantiated.
-- SLR PR #75: protected fleet candidate-only; NOT proof discharge.
--
-- No foreign module is imported into this Agda compilation unit.
-- Cross-repo names are exact external LOCATORS, not kernel evidence.
-- No case proceeding filed or signed approval/95C acquired.
------------------------------------------------------------------------

woogarooMatter : String
woogarooMatter = "matter:au:epbc:2019-8575:postapproval"

sensiblawCandidateContract : String
sensiblawCandidateContract = "woogaroo-case-cut:v0_1"

data PaymentRole : Set where
  sourceLocatorOnly : PaymentRole
  statutoryDutyDefined : PaymentRole
  reviewedExactSourceSpan : PaymentRole
  reviewedCaseWitness : PaymentRole
  competentCourtDetermination : PaymentRole

record NativeMatterInterop : Set where
  constructor native-matter-interop
  field
    nativeGround : Case.CaseHypothesis
    externalSensiblawGroundRef : String
    externalSLRResidualRef : Maybe String
    matchedEPBCAction : String
    requestedNextOriginal : String
    claimedRole : PaymentRole
    persistedSpanPaid : Bool
    caseWitnessPaid : Bool
    reviewerPaid : Bool
    courtDeterminationPaid : Bool
    failClosedSpan : persistedSpanPaid ≡ false
    failClosedWitness : caseWitnessPaid ≡ false
    failClosedReview : reviewerPaid ≡ false
    failClosedCourt : courtDeterminationPaid ≡ false
open NativeMatterInterop public

adviceBridge : NativeMatterInterop
adviceBridge = native-matter-interop
  Case.adviceGround "candidate-ground:advice-consideration"
  (just "residual:woogaroo:correct-advice-consideration")
  "2019/8575"
  "Original 15 Oct signed approval/conditions; Secretary s95C report and actual delegate s139(2) approved koala advice consideration."
  sourceLocatorOnly false false false false refl refl refl refl

recoveryBridge : NativeMatterInterop
recoveryBridge = native-matter-interop
  Case.recoveryGround "candidate-ground:recovery-plan" nothing
  "2019/8575"
  "Binding original national koala recovery plan provisions and signed condition consistency."
  sourceLocatorOnly false false false false refl refl refl refl

baselineBridge : NativeMatterInterop
baselineBridge = native-matter-interop
  Case.actionImpactGround "candidate-ground:incremental-habitat"
  (just "residual:woogaroo:habitat-function-vs-retained-width")
  "2019/8575"
  "Same-action approved polygon; Item 4.6(c) final PD; mature-tree, connectivity and corridor function evidence against Stockland publisher claim."
  sourceLocatorOnly false false false false refl refl refl refl

commentBridge : NativeMatterInterop
commentBridge = native-matter-interop
  Case.commentsGround "candidate-ground:comment-transmission" nothing
  "2019/8575"
  "Original proponent 2026 inbox logs and section95B copies of all actually received comments, plus s95C report."
  sourceLocatorOnly false false false false refl refl refl refl

scopeBridge : NativeMatterInterop
scopeBridge = native-matter-interop
  Case.scopeGround "candidate-ground:approval-scope" nothing
  "2019/8575"
  "Original signed approval conditions, clearing coordinates, delegation and planning transition version."
  sourceLocatorOnly false false false false refl refl refl refl

prestartBridge : NativeMatterInterop
prestartBridge = native-matter-interop
  Case.localPrestartGround "candidate-ground:local-prestart" nothing
  "2019/8575"
  "Same-stage 9281/2024/OW Condition6(a) submission and Council written acceptance; actual works event."
  sourceLocatorOnly false false false false refl refl refl refl

politicalBridge : NativeMatterInterop
politicalBridge = native-matter-interop
  Case.politicalTheory "candidate-ground:improper-influence" nothing
  "2019/8575"
  "Actual 15 October decision-specific direct communication, conflict or transaction and applicable legal duty; historical shareholder/gas adjacency does not pay it."
  sourceLocatorOnly false false false false refl refl refl refl

slrWoogarooCandidateCut : List NativeMatterInterop
slrWoogarooCandidateCut =
  adviceBridge ∷ recoveryBridge ∷ baselineBridge ∷
  commentBridge ∷ scopeBridge ∷ prestartBridge ∷ politicalBridge ∷ []

-- Reused case research, not re-minted statutes.
originalAdviceCaseHypothesis : Case.CaseHypothesis
originalAdviceCaseHypothesis = Case.adviceGround

originalStandingEvidenceGate : Counsel.LitigationGate
originalStandingEvidenceGate = Counsel.organisationStanding

originalSecretaryFileGate : File.DecisionFileReceipt
originalSecretaryFileGate = File.section95CRecommendation

originalRegionalAssessmentResidual : Cumulative.CumulativeResponseResidual
originalRegionalAssessmentResidual = Cumulative.locatedLocalRegionalIntegrationResidual

originalCouncilPrestartAcceptance : Council.Condition6aEvidenceObject
originalCouncilPrestartAcceptance = Council.condition6aCouncilAcceptance

data GitHubSourceLocatorEqualsPersistedLegalRevision : Set where
data SourceAdmissionCompileEligibleEqualsPaidExactSpan : Set where
data RelatedScenic20208651SubmissionEqualsSpringviewMerits : Set where
data SLRUnreviewedFixtureEqualsPersistedControversy : Set where
data SLRCandidateResidualEqualsReviewedProofPayment : Set where
data AGDARectypeEqualsKernelVerification : Set where
data StatisticalOrFinancialOverlapEqualsImproperInfluence : Set where
data NoPhysicalCommencementDateEqualsNoThreatEver : Set where
data HypotheticalGovernmentReplyEqualsActuallyAdmittedPosition : Set where
data OtherPartyCourtFilingEqualsThisMatterFiling : Set where

locatorNotPersistedRevision : GitHubSourceLocatorEqualsPersistedLegalRevision → ⊥
locatorNotPersistedRevision ()

compileEligibleNotSpanPaid : SourceAdmissionCompileEligibleEqualsPaidExactSpan → ⊥
compileEligibleNotSpanPaid ()

scenicActivitiesNotSameMerits : RelatedScenic20208651SubmissionEqualsSpringviewMerits → ⊥
scenicActivitiesNotSameMerits ()

unreviewedFixtureNotPersisted : SLRUnreviewedFixtureEqualsPersistedControversy → ⊥
unreviewedFixtureNotPersisted ()

candidateResidualNotReviewed : SLRCandidateResidualEqualsReviewedProofPayment → ⊥
candidateResidualNotReviewed ()

agdaRecordNotKernelCheck : AGDARectypeEqualsKernelVerification → ⊥
agdaRecordNotKernelCheck ()

financialAdjacencyNotImproperInfluence :
  StatisticalOrFinancialOverlapEqualsImproperInfluence → ⊥
financialAdjacencyNotImproperInfluence ()

noPublishedStartNotNever : NoPhysicalCommencementDateEqualsNoThreatEver → ⊥
noPublishedStartNotNever ()

hypotheticalReplyNotAdmission :
  HypotheticalGovernmentReplyEqualsActuallyAdmittedPosition → ⊥
hypotheticalReplyNotAdmission ()

otherCourtCaseNotFiledHere : OtherPartyCourtFilingEqualsThisMatterFiling → ⊥
otherCourtCaseNotFiledHere ()
