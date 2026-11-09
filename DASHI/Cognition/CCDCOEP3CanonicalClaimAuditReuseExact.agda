module DASHI.Cognition.CCDCOEP3CanonicalClaimAuditReuseExact where

------------------------------------------------------------------------
-- CANONICAL SOURCE / PNF / DESIGN / INDEPENDENCE REUSE.
-- No new source/admissibility/evidence-coding calculus is introduced.
--
-- Original author, publisher and archive claims stay attributable to
-- their original parties. DASHI only joins its pre-existing evidence
-- owners to the case-indexed CCDCOE six-gate consumer.
--
-- IMPORTANT: this module provides a proof *contract*, not independently
-- verified historical source material, causal effects or intent.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.EmpiricalSourceDiligenceAdmissionExact as Source
import DASHI.Core.EvidenceHyperfabricExact as Hyper
import DASHI.Reasoning.EvidenceDesignAdmissibilityExact as Design
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Cognition.CCDCOEP3SameOperationIndexedAdmissionExact as Case

-- Canonical historical source admission is already owned by Source.
-- Canonical obligation-relative design admission is already owned by
-- Design, not by a fresh CCDCOE-specific source-status enumeration.
--
-- Stage-specific keys are supplied by the consuming empirical study.
-- The equalities prevent moving a valid study design audit onto a
-- DIFFERENT diligence claim or onto a different obligation key.
record CanonicalStagePayment
    (claimKey : Case.OriginalCase → Case.EvidenceStage → String)
    (c : Case.OriginalCase)
    (stage : Case.EvidenceStage)
    (fact : Source.EmpiricalFactAdmission) : Set where
  field
    assessment : Design.EvidenceForObligation
    designAdmissible :
      Design.AdmissibleForPromotion
        (Design.EvidenceForObligation.finding assessment)
    diligenceClaimMatchesStage :
      Source.SourceDiligence.claimReference
        (Source.EmpiricalFactAdmission.diligence fact) ≡
      claimKey c stage
    boundedPropositionMatchesStage :
      Source.EmpiricalFactAdmission.boundedPropositionReference fact ≡
      claimKey c stage
    designObligationMatchesStage :
      PNF.AssertionObligation.parentAssertion
        (Design.EvidenceForObligation.obligation assessment) ≡
      claimKey c stage

-- No new admission record: specialise the EXISTING ClaimBoundAdmission
-- to the repo-wide EmpiricalFactAdmission and EvidenceForObligation.
CanonicalClaimAdmission :
  (E : Case.OriginalCase → Case.EvidenceStage → Set) →
  (sourceCase : Source.EmpiricalFactAdmission → Case.OriginalCase) →
  (claimKey : Case.OriginalCase → Case.EvidenceStage → String) →
  Case.OriginalCase → Set
CanonicalClaimAdmission E sourceCase claimKey c =
  Case.ClaimBoundAdmission E Source.EmpiricalFactAdmission sourceCase
    (CanonicalStagePayment claimKey) c

canonicalAdmissionImpliesSixGates :
  (E : Case.OriginalCase → Case.EvidenceStage → Set)
  (sourceCase : Source.EmpiricalFactAdmission → Case.OriginalCase)
  (claimKey : Case.OriginalCase → Case.EvidenceStage → String)
  (c : Case.OriginalCase) →
  CanonicalClaimAdmission E sourceCase claimKey c →
  Case.AdmitsOneOriginalCase E c
canonicalAdmissionImpliesSixGates E sourceCase claimKey c =
  Case.claimBoundImpliesStageAdmission E Source.EmpiricalFactAdmission
    sourceCase (CanonicalStagePayment claimKey) c

canonicalAdmissionRequiresStageDesignPayment :
  (E : Case.OriginalCase → Case.EvidenceStage → Set)
  (sourceCase : Source.EmpiricalFactAdmission → Case.OriginalCase)
  (claimKey : Case.OriginalCase → Case.EvidenceStage → String)
  (c : Case.OriginalCase)
  (admitted : CanonicalClaimAdmission E sourceCase claimKey c)
  (stage : Case.EvidenceStage) →
  Design.AdmissibleForPromotion
    (Design.EvidenceForObligation.finding
      (CanonicalStagePayment.assessment
        (Case.ClaimBoundAdmission.claimSupported admitted stage)))
canonicalAdmissionRequiresStageDesignPayment E sourceCase claimKey c admitted stage =
  CanonicalStagePayment.designAdmissible
    (Case.ClaimBoundAdmission.claimSupported admitted stage)

canonicalAdmissionBlockedByMissingExposure :
  (E : Case.OriginalCase → Case.EvidenceStage → Set)
  (sourceCase : Source.EmpiricalFactAdmission → Case.OriginalCase)
  (claimKey : Case.OriginalCase → Case.EvidenceStage → String)
  (c : Case.OriginalCase) →
  (E c Case.recipientExposure → ⊥) →
  CanonicalClaimAdmission E sourceCase claimKey c → ⊥
canonicalAdmissionBlockedByMissingExposure E sourceCase claimKey c =
  Case.claimBoundMissingExposureBlocks E Source.EmpiricalFactAdmission
    sourceCase (CanonicalStagePayment claimKey) c

-- Claim-specific support is NOT independent corroboration. Reuse the
-- existing Hyperfabric CorroborationGraph and IndependentCorroboration
-- rather than creating a parallel source-independence predicate.
sharedLineageCannotPayIndependentCorroboration :
  {Evidence : Set}
  (graph : Hyper.CorroborationGraph Evidence)
  (left right : Evidence) →
  Hyper.CorroborationGraph.sourceRelation graph left right ≡
    Hyper.sharedLineage →
  Hyper.IndependentCorroboration graph left right → ⊥
sharedLineageCannotPayIndependentCorroboration graph left right sameLineage corroboration =
  Hyper.independent≠sharedLineage
    (trans (sym (proj₂ corroboration)) sameLineage)

-- Independent-corroboration, claim-level design admission and
-- six-stage operation admission remain THREE distinct obligations.
-- No historical GCC sample, exposure, counterfactual or intent proof
-- is introduced or inferred by these generic transport lemmas.
