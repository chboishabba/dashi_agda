module DASHI.Law.SensibLawWoogarooDialecticTrialecticSynthesis20261028Exact where

------------------------------------------------------------------------
-- WOOGAROO 2019/8575: dialectical / trialectic synthesis consumer.
--
-- Canonical reuse:
--   * SensibLawDialecticalProofSearchExact (paired probes / discriminator)
--   * SensibLawAdversarialProofSearchRuntimeExact (defeater rerun)
--   * TrialecticAttachedTwoCellExact (edge boundary + independent face)
--   * TrialecticBoundaryFaceNonfactorabilityExact (face non-descent)
--   * SensibLawWoogarooAdversarialLogicalTests20261028Exact (7 grounds)
--   * prior Pareto / Ibrahim source-genealogy owners via the latter.
--
-- The "third" locus is independent evidentiary/legal/physical appraisal,
-- NOT a third litigant or a new legal authority. Neither a majority of
-- edges nor a valid propositional implication fills the trialectic face.
-- Synthesis is a candidate workflow/output, not judicial disposition.
--
-- Credit: original EPBC legislation and courts; primary source authors
-- QUT / SWFG / DCCEEW / Stockland; prior DASHI dialectic/trialectic,
-- historical SensibLaw prototype, SLR Matter, Ibrahim/Monster 3B authors.
-- Case integration: user-directed / ChatGPT-assisted, 28 October 2026.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Reasoning.TrialecticBoundaryFaceNonfactorabilityExact as Face
import DASHI.Reasoning.TrialecticAttachedTwoCellExact as Attached
import DASHI.Reasoning.TrialecticEdgeSynthesisCompatibilityExact as Edges
import DASHI.Reasoning.TrialecticLocalLogicQualificationExact as Local
import DASHI.Reasoning.DialecticalOppositionNonExplosionExact as Opposition
import DASHI.Law.SensibLawDialecticalProofSearchExact as Dialectic
import DASHI.Law.SensibLawAdversarialProofSearchRuntimeExact as Search
import DASHI.Law.SensibLawWoogarooAdversarialLogicalTests20261028Exact as Adversarial
import DASHI.Law.SensibLawWoogarooEPBC8575PleadableGroundsPrecedentCut20261028Exact as Case

------------------------------------------------------------------------
-- Preserve original thesis, opposing party and independent assessment.
------------------------------------------------------------------------

data WoogarooSynthesisKind : Set where
  seekOriginals : WoogarooSynthesisKind
  applicantHypothesisForDefeaterSearch : WoogarooSynthesisKind
  respondentHypothesisForCounterDefeaterSearch : WoogarooSynthesisKind
  reconcileOpposingSourceAssertions : WoogarooSynthesisKind

-- A contradiction is a review target, not a logical refutation or
-- a licence to select whichever side seems more plausible.
classify : ∀ {g} → Adversarial.HypotheticalWorld g →
  WoogarooSynthesisKind
classify w with Adversarial.contradictionPresent w
... | true = reconcileOpposingSourceAssertions
... | false with Adversarial.applicantConditional w
...   | true = applicantHypothesisForDefeaterSearch
...   | false with Adversarial.respondentConditional w
...     | true = respondentHypothesisForCounterDefeaterSearch
...     | false = seekOriginals

dialecticalNextRole : WoogarooSynthesisKind → Search.AdversarialRole
dialecticalNextRole seekOriginals = Search.nextRole Search.missingAtoms
dialecticalNextRole applicantHypothesisForDefeaterSearch =
  Search.nextRole Search.reachableCandidate
dialecticalNextRole respondentHypothesisForCounterDefeaterSearch =
  Search.nextRole Search.defeated
dialecticalNextRole reconcileOpposingSourceAssertions =
  Search.nextRole Search.contested

-- Edges preserve the first-order provisional for/against contrast.
-- Independent third-party appraisal has not been paid in this case:
-- BC and CA stay neutral, whatever the hypothetical applicant/defence test.
oppositionEdge : WoogarooSynthesisKind → Face.EdgeDisposition
oppositionEdge seekOriginals = Face.neutralEdge
oppositionEdge applicantHypothesisForDefeaterSearch = Face.positiveEdge
oppositionEdge respondentHypothesisForCounterDefeaterSearch = Face.negativeEdge
oppositionEdge reconcileOpposingSourceAssertions = Face.neutralEdge

trialecticBoundary : WoogarooSynthesisKind → Face.TrialecticBoundary
trialecticBoundary kind =
  Face.trialectic-boundary
    (oppositionEdge kind)
    Face.neutralEdge
    Face.neutralEdge

-- The face is a separate relational cell, NOT computed from the edges.
-- The actual Woogaroo decision file, same-scope transport and competent
-- independent review are not present as source-paid witnesses.
unpaidTrialectic : WoogarooSynthesisKind → Attached.TrialecticAttachedTwoCell
unpaidTrialectic kind =
  Attached.trialectic-attached-two-cell
    (trialecticBoundary kind)
    Face.underdeterminedFace

faceStillUnresolved : (kind : WoogarooSynthesisKind) →
  Attached.attachedFace (unpaidTrialectic kind) ≡ Face.underdeterminedFace
faceStillUnresolved kind = refl

-- Existing theorem: no extraction of the 2-cell from the 1-skeleton.
threeEdgesDoNotDetermineIndependentFace :
  Descent.FactorsThrough
    Attached.attachedBoundaryObserver Attached.attachedFaceConsumer → ⊥
threeEdgesDoNotDetermineIndependentFace =
  Attached.attachedFaceDoesNotFactorThroughBoundary

-- Directly consume existing compatible synthetic edge family as a
-- method-only reference; it carries no fact about this EPBC action.
canonicalCompatibleEdges : Edges.CompatibleDialecticalTriangle
canonicalCompatibleEdges = Edges.canonicalCompatibleDialecticalTriangle

canonicalNonExplosion :
  Opposition.DialecticalOppositionBoundary
canonicalNonExplosion = Opposition.canonicalDialecticalOppositionBoundary

canonicalLocalScopeRule : Local.TrialecticLocalLogicBoundary
canonicalLocalScopeRule = Local.canonicalTrialecticLocalLogicBoundary

canonicalDialecticalSearch :
  Dialectic.DialecticalSearchBoundary
canonicalDialecticalSearch = Dialectic.canonicalDialecticalSearchBoundary

------------------------------------------------------------------------
-- Typed synthesis output: what was asserted, what could defeat it,
-- and which original would discriminate without erasing either voice.
------------------------------------------------------------------------

hypothesis : Case.Ground → Case.CaseHypothesis
hypothesis Case.approvedAdviceOmitted = Case.adviceGround
hypothesis Case.recoveryPlanConflict = Case.recoveryGround
hypothesis Case.actionBaselineError = Case.actionImpactGround
hypothesis Case.commentTransmissionOrProcedure = Case.commentsGround
hypothesis Case.scopeOrUncertainConditions = Case.scopeGround
hypothesis Case.sameStageCondition6aBreach = Case.localPrestartGround
hypothesis Case.improperPoliticalFinancialInfluence = Case.politicalTheory

record WoogarooSynthesisOutput : Set where
  constructor synthesis-output
  field
    ground : Case.Ground
    candidateOutcome : WoogarooSynthesisKind
    dialecticalNext : Search.AdversarialRole
    trialectic : Attached.TrialecticAttachedTwoCell
    applicantSourceRule : String
    respondentCountercase : String
    decisiveOriginals : String
    countercaseFalsifier : String
    synthesisedEvidenceQuery : Dialectic.SearchDiscriminator
    authorityIsActualCourtFinding : Bool
    authorityIsActualReviewPayment : Bool
    courtFindingIsFalse : authorityIsActualCourtFinding ≡ false
    reviewPaymentIsFalse : authorityIsActualReviewPayment ≡ false

open WoogarooSynthesisOutput public

makeDiscriminator : Case.Ground → Dialectic.SearchDiscriminator
makeDiscriminator g =
  Dialectic.searchDiscriminator
    (Adversarial.groundKey g)
    (Case.hook (hypothesis g))
    (Case.bestDefence (hypothesis g))
    (Case.proofNeeded (hypothesis g))
    (Adversarial.groundKey g)

synthesise : (g : Case.Ground) →
  Adversarial.HypotheticalWorld g → WoogarooSynthesisOutput
synthesise g w =
  synthesis-output
    g
    (classify w)
    (dialecticalNextRole (classify w))
    (unpaidTrialectic (classify w))
    (Case.hook (hypothesis g))
    (Case.bestDefence (hypothesis g))
    (Case.proofNeeded (hypothesis g))
    (Case.falsifier (hypothesis g))
    (makeDiscriminator g)
    false false refl refl

-- The actual case is no more advanced than source-unpaid hypotheses.
-- false is "not established to this workflow", not "factually false".
unpaidInput : (g : Case.Ground) → Adversarial.HypotheticalWorld g
unpaidInput g = Adversarial.world false false false false false false

unpaidSynthesis : (g : Case.Ground) → WoogarooSynthesisOutput
unpaidSynthesis g = synthesise g (unpaidInput g)

unpaidNeedsOriginals : (g : Case.Ground) →
  candidateOutcome (unpaidSynthesis g) ≡ seekOriginals
unpaidNeedsOriginals g = refl

unpaidCannotForceFace : (g : Case.Ground) →
  Attached.attachedFace (trialectic (unpaidSynthesis g))
    ≡ Face.underdeterminedFace
unpaidCannotForceFace g = refl

contradictionGoesToReview :
  candidateOutcome
    (synthesise Case.approvedAdviceOmitted
      Adversarial.contradictoryWorld)
    ≡ reconcileOpposingSourceAssertions
contradictionGoesToReview = refl

applicantHypothesisNotJudgment :
  authorityIsActualCourtFinding
    (synthesise Case.approvedAdviceOmitted
      (Adversarial.applicantWorld Case.approvedAdviceOmitted))
    ≡ false
applicantHypothesisNotJudgment = refl

defenceHypothesisNotPayment :
  authorityIsActualReviewPayment
    (synthesise Case.approvedAdviceOmitted
      (Adversarial.respondentWorld Case.approvedAdviceOmitted))
    ≡ false
defenceHypothesisNotPayment = refl

-- Seven source-indexed candidate synthesis packets, not filings or orders.
allSevenUnpaidOutputs : List WoogarooSynthesisOutput
allSevenUnpaidOutputs =
  unpaidSynthesis Case.approvedAdviceOmitted ∷
  unpaidSynthesis Case.recoveryPlanConflict ∷
  unpaidSynthesis Case.actionBaselineError ∷
  unpaidSynthesis Case.commentTransmissionOrProcedure ∷
  unpaidSynthesis Case.scopeOrUncertainConditions ∷
  unpaidSynthesis Case.sameStageCondition6aBreach ∷
  unpaidSynthesis Case.improperPoliticalFinancialInfluence ∷ []
