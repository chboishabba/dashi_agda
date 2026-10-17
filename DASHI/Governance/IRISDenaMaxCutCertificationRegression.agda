module DASHI.Governance.IRISDenaMaxCutCertificationRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto
import DASHI.Governance.OriginalThreadParetoMaxCut20261008Exact as MaxCut
import DASHI.Governance.IRISDenaMaxCutSourceGuardExact as Guard
import DASHI.Governance.IRISDenaCorrectionAwareReviewGateExact as Review
import DASHI.Governance.AUKUSUSPersonnelExchangeAuthorityEnvelopeExact as PEP
import DASHI.Governance.IRISDenaBunkClaimRevisionConflictExact as Bunks
import DASHI.Governance.IRISDenaObserverHierarchyNonDescentExact as Hierarchy

------------------------------------------------------------------------
-- Focused certification regression.
--
-- This owner deliberately adds no new political or historical conclusion.
-- It pins the current max-cut, unpaid source/review coordinates and the
-- non-substitutability of the evidence observers so an exact-head kernel
-- checker has one compact terminal target.
------------------------------------------------------------------------

frontierStillExactlyThreeIRISCells :
  Pareto.paretoFrontier MaxCut.livePortfolio ≡
    MaxCut.hansardContentCell
    ∷ MaxCut.embeddingProtocolCell
    ∷ MaxCut.exactOperationalCell
    ∷ []
frontierStillExactlyThreeIRISCells = MaxCut.frontierExactlyIRISThreeStage

sourceAuthorityStillFailClosed :
  Guard.SourceGuard.hansardDutyContentPrimaryPaid Guard.canonicalGuard ≡ false
  × Guard.SourceGuard.hansardExactReviewBindingPaid Guard.canonicalGuard ≡ false
  × Guard.SourceGuard.directivePrimaryPaid Guard.canonicalGuard ≡ false
  × Guard.SourceGuard.paretoMayUpgradeAuthority Guard.canonicalGuard ≡ false
sourceAuthorityStillFailClosed = refl , refl , refl , refl

reviewLeafStillUnpaid :
  Review.CorrectionAwareReviewDemand.transcriptContentAcquired Review.canonicalReviewDemand ≡ false
  × Review.CorrectionAwareReviewDemand.correctionContentAcquired Review.canonicalReviewDemand ≡ false
  × Review.CorrectionAwareReviewDemand.applicableCorrectionResolved Review.canonicalReviewDemand ≡ false
  × Review.CorrectionAwareReviewDemand.exactReviewBindingPaid Review.canonicalReviewDemand ≡ false
  × Review.CorrectionAwareReviewDemand.dutyClassPromotionPaid Review.canonicalReviewDemand ≡ false
reviewLeafStillUnpaid = refl , refl , refl , refl , refl

genericPEPStillDoesNotCloseBilateralOrEpisode :
  PEP.USPEPAuthorityEnvelopeReceipt.bilateralMOUOperativeTextPaid PEP.canonicalEnvelope ≡ false
  × PEP.USPEPAuthorityEnvelopeReceipt.ranDirectivePrimaryTextPaid PEP.canonicalEnvelope ≡ false
  × PEP.USPEPAuthorityEnvelopeReceipt.irisSameEpisodeDutyPaid PEP.canonicalEnvelope ≡ false
genericPEPStillDoesNotCloseBilateralOrEpisode = refl , refl , refl

bunkRevisionStillDoesNotRevealExactDuty :
  Bunks.BunkClaimRevisionReceipt.bunkPropositionPrimaryDenied Bunks.canonicalRevision ≡ true
  × Bunks.BunkClaimRevisionReceipt.exactDutyDisclosedByDenial Bunks.canonicalRevision ≡ false
  × Bunks.BunkClaimRevisionReceipt.historicalEventChangedByLaterSource Bunks.canonicalRevision ≡ false
bunkRevisionStillDoesNotRevealExactDuty = refl , refl , refl

-- The theorem-bearing non-descent owners remain the reason that paying a
-- duty-class or protocol cell cannot substitute for the exact-task record.
dutyClassNonSubstitution = Hierarchy.verifiedDutyClassCannotSubstituteExactTask
protocolNonSubstitution = Hierarchy.completeProtocolCannotSubstituteExactTask
