{-# OPTIONS --safe #-}
module DASHI.Unified.TOECurrentMaxCutGovernanceFleetRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Unified.TOECurrentMaxCutGovernanceFleetExact as Cut
import DASHI.Core.AuthorityNonPromotionCore as Authority

gate4TargetRemains58 :
  Cut.gate4FormalGapCount ≡ 58
gate4TargetRemains58 = Cut.gate4FormalGapCountIs58

fleetReportedTargetRemains58 :
  Cut.fleetReportedFormalGapCount ≡ 58
fleetReportedTargetRemains58 = Cut.fleetReportedFormalGapCountIs58

dischargedFleetFibresRemainExcluded :
  Cut.dischargedFleetFibresExcluded ≡ true
dischargedFleetFibresRemainExcluded = refl

fleetPriorityDoesNotCreateProof :
  Cut.fleetPriorityCreatesProof ≡ false
fleetPriorityDoesNotCreateProof = refl

candidateLegalSourceDoesNotCreateAuthority :
  Cut.candidateLegalSourceCreatesAuthority ≡ false
candidateLegalSourceDoesNotCreateAuthority = refl

legalAuthorityDoesNotCreateApplicability :
  Cut.legalAuthorityCreatesApplicability ≡ false
legalAuthorityDoesNotCreateApplicability = refl

formalGovernanceDoesNotCreatePoliticalLegitimacy :
  Cut.formalGovernanceCreatesPoliticalLegitimacy ≡ false
formalGovernanceDoesNotCreatePoliticalLegitimacy = refl

finiteRGDoesNotCreateContinuumPromotion :
  Cut.finiteRGCreatesContinuumPromotion ≡ false
finiteRGDoesNotCreateContinuumPromotion = refl

ibrahimSearchPriorityDoesNotCreateRecognition :
  Cut.ibrahimPriorityCreatesRecognition ≡ false
ibrahimSearchPriorityDoesNotCreateRecognition = refl

esdRemainsReadOnly :
  Cut.esdSurfaceEdited ≡ false
esdRemainsReadOnly = refl


-- Source-owned promotion policy is reachable through the TOE consumer.
semanticPromotionCannotCreateLegalAuthority :
  Authority.legalAuthorityFlag Cut.toeSemanticPromotionAuthorityBoundary ≡ false
semanticPromotionCannotCreateLegalAuthority =
  Cut.toeSemanticPromotionCannotCreateLegalAuthority

semanticPromotionCannotCreateAnyAuthority :
  Authority.promotesAnyAuthority Cut.toeSemanticPromotionAuthorityBoundary ≡ false
semanticPromotionCannotCreateAnyAuthority =
  Cut.toeSemanticPromotionCannotCreateAnyAuthority

allCanonicalAuthorityKindsRemainClosed :
  Authority.AllAuthorityKindsFalse
    Authority.canonicalAuthorityNonPromotionBundle
    Authority.canonicalAuthorityKinds
allCanonicalAuthorityKindsRemainClosed =
  Cut.toeCanonicalAuthorityKindsRemainClosed

------------------------------------------------------------------------
-- Governance and future-safety regression.
------------------------------------------------------------------------

staticRefinementStillDoesNotCreateDynamicSafety :
  Cut.staticRefinementCreatesDynamicSafety ≡ false
staticRefinementStillDoesNotCreateDynamicSafety = refl

frozenSelectionStillDoesNotCreateDynamicSafety :
  Cut.frozenRuleCreatesDynamicSafety ≡ false
frozenSelectionStillDoesNotCreateDynamicSafety = refl

provenanceStillDoesNotCreateTruthOrAuthority :
  Cut.provenanceCreatesTruthOrAuthority ≡ false
provenanceStillDoesNotCreateTruthOrAuthority = refl

kernelClosureStillDoesNotCreateSemanticClosure :
  Cut.kernelClosureCreatesSemanticClosure ≡ false
kernelClosureStillDoesNotCreateSemanticClosure = refl


------------------------------------------------------------------------
-- 369 contextual sheet/cube/fibre regression.
------------------------------------------------------------------------

decisionSheetRemainsNine :
  Cut.decisionSheetStateCount ≡ 9
decisionSheetRemainsNine =
  Cut.decisionSheetStateCountIsNine

interactionCubeRemainsTwentySeven :
  Cut.interactionCubeStateCount ≡ 27
interactionCubeRemainsTwentySeven =
  Cut.interactionCubeStateCountIsTwentySeven

appraisalFibreRemainsSevenHundredTwentyNine :
  Cut.appraisalFibreStateCount ≡ 729
appraisalFibreRemainsSevenHundredTwentyNine =
  Cut.appraisalFibreStateCountIsSevenHundredTwentyNine

supportRemainsPositive :
  Cut.relativeOrientationTrit Cut.Trajectory.supports
  ≡ Cut.SSP.sspPosOne
supportRemainsPositive =
  Cut.supportOrientationIsPositive

counterRemainsNegative :
  Cut.relativeOrientationTrit Cut.Trajectory.counters
  ≡ Cut.SSP.sspNegOne
counterRemainsNegative =
  Cut.counterOrientationIsNegative

synthesisDoesNotEraseComparator :
  Cut.synthesisErasesComparator ≡ false
synthesisDoesNotEraseComparator =
  Cut.synthesisErasesComparatorIsFalse

contextualFibreWeldReceiptReachable :
  Cut.TOE369ContextualFibreWeldReceipt
contextualFibreWeldReceiptReachable =
  Cut.canonicalTOE369ContextualFibreWeldReceipt
