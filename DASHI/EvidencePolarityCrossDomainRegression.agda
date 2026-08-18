module DASHI.EvidencePolarityCrossDomainRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Algebra.ClaimIndexedEvidencePolarityExact as Indexed
import DASHI.Algebra.DisagreementFourViewBoundary as Four
import DASHI.Biology.BrainProxyEvidenceAuthorityBridgeExact as Brain
import DASHI.Biology.IntersectionalClaimEvidenceFibreExact as Intersectional
import DASHI.Chemistry.EvidenceObligationAuthorityBridgeExact as Chemistry
import DASHI.Core.EvidenceObligationAuthoritySeparationExact as Governed
import DASHI.Physics.Chemistry.AtomicEvidenceObligationBridgeExact as Atomic
import DASHI.Reasoning.HyperfabricHypervoxelEvidencePolarityBridgeExact as Hyper

------------------------------------------------------------------------
-- Focused compile/regression surface for the cross-domain evidence tranche.
------------------------------------------------------------------------

conflictStillRetained :
  Indexed.conflict ≡ Four.assess true true
conflictStillRetained = Indexed.conflictIsBoth

supportAloneStillCannotPromote :
  Governed.promotionGate Governed.supportOnlyOpenDenied ≡ false
supportAloneStillCannotPromote = Governed.supportDoesNotDischargeObligations

conflictStillCannotPromoteAffirmatively :
  Governed.promotionGate Governed.conflictDischargedGranted ≡ false
conflictStillCannotPromoteAffirmatively =
  Governed.conflictDoesNotBecomeAffirmativePromotion

brainProxySupportStillNonPromoting :
  Governed.promotionGate Brain.proxyObservationSupportedOnly ≡ false
brainProxySupportStillNonPromoting = Brain.proxySupportDoesNotPromoteHiddenState

chemistrySupportStillNonPromoting :
  Governed.promotionGate Chemistry.chemistryCandidateSupportedButNotPromotable
  ≡ false
chemistrySupportStillNonPromoting =
  Chemistry.chemistryCandidateSupportDoesNotPromote

atomicSupportStillNonPromoting :
  Governed.promotionGate Atomic.atomicCandidateSupportedOnly ≡ false
atomicSupportStillNonPromoting =
  Atomic.atomicCandidateSupportDoesNotPromoteRecovery

intersectionalContextAlignmentRequired :
  Intersectional.IntersectionalClaimEvidenceBoundary.explicitAlignmentRequiredAcrossContexts
    Intersectional.canonicalIntersectionalClaimEvidenceBoundary
  ≡ true
intersectionalContextAlignmentRequired = refl

hyperfabricDoesNotDiagnose :
  Hyper.HyperfabricHypervoxelEvidenceBoundary.hyperfabricAutomaticallyDiagnosesClaimed
    Hyper.canonicalHyperfabricHypervoxelEvidenceBoundary
  ≡ false
hyperfabricDoesNotDiagnose = refl
