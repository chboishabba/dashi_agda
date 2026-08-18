module DASHI.EvidencePolarityCrossDomainRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Algebra.ClaimIndexedEvidencePolarityExact as Indexed
import DASHI.Algebra.DisagreementFourViewBoundary as Four
import DASHI.Biology.BrainProxyEvidenceAuthorityBridgeExact as Brain
import DASHI.Biology.IntersectionalClaimEvidenceFibreExact as Intersectional
import DASHI.Chemistry.EvidenceObligationAuthorityBridgeExact as Chemistry
import DASHI.Core.EvidenceObligationAuthoritySeparationExact as Governed
import DASHI.Physics.Chemistry.AtomicEvidenceObligationBridgeExact as Atomic
import DASHI.Reasoning.HyperfabricHypervoxelEvidencePolarityBridgeExact as Hyper
import DASHI.Reasoning.RelationalLensSynthesisCore as Lens

------------------------------------------------------------------------
-- Focused compile/regression surface for the cross-domain evidence tranche.
------------------------------------------------------------------------

conflictStillRetained :
  Indexed.conflict ≡ Four.assess true true
conflictStillRetained = Indexed.conflictIsBoth

contextualCounterpositionStillNotLogicalNegation :
  Lens.contextualCounterpositionRole ≡ Lens.logicalNegationRole → ⊥
contextualCounterpositionStillNotLogicalNegation =
  Indexed.contextualCounterpositionRoleIsNotLogicalNegation

orientationReversalStillNotLogicalNegation :
  Lens.orientationReversalRole ≡ Lens.logicalNegationRole → ⊥
orientationReversalStillNotLogicalNegation =
  Indexed.orientationReversalRoleIsNotLogicalNegation

opposingSupportDoesNotSelfQualifyAsNegation :
  Indexed.ClaimIndexedEvidencePolarityBoundary.opposingSupportAutomaticallyMeansLogicalNegation
    Indexed.canonicalClaimIndexedEvidencePolarityBoundary
  ≡ false
opposingSupportDoesNotSelfQualifyAsNegation = refl

supportStillLeavesObligationOpen :
  Governed.obligations Governed.supportOnlyOpen ≡ Governed.obligationsOpen
supportStillLeavesObligationOpen = Governed.supportDoesNotDischargeObligations

dischargedTechnicalObligationsStillCannotOpenLocalAuthority :
  Governed.localPromotion Governed.supportOnlyDischarged ≡ false
dischargedTechnicalObligationsStillCannotOpenLocalAuthority =
  Governed.dischargedObligationsDoNotOpenAuthorityGate

conflictStillCannotOpenAuthority :
  Governed.localPromotion Governed.conflictDischarged ≡ false
conflictStillCannotOpenAuthority = Governed.conflictDoesNotOpenAuthorityGate

brainProxySupportStillNonPromoting :
  Governed.localPromotion Brain.proxyObservationSupportedOnly ≡ false
brainProxySupportStillNonPromoting = Brain.proxySupportDoesNotPromoteHiddenState

chemistrySupportStillNonPromoting :
  Governed.localPromotion Chemistry.chemistryCandidateSupportedButNotPromotable
  ≡ false
chemistrySupportStillNonPromoting =
  Chemistry.chemistryCandidateSupportDoesNotPromote

atomicSupportStillNonPromoting :
  Governed.localPromotion Atomic.atomicCandidateSupportedOnly ≡ false
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
