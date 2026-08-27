module DASHI.Governance.AuthorityRepairLegitimacySeparationExact where

------------------------------------------------------------------------
-- AUTHORITY / REPAIR / LEGITIMACY SEPARATION
--
-- Cross-pollinates the existing authority/option-cone seam with Sen-style
-- capability/functioning and Beetham-style legitimacy evidence. The exact
-- finite witnesses are DASHI constructions; they do not adjudicate any live
-- authority, intervention, or institution.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Governance.LegitimacyEvidenceSeparationExact as Legitimacy

data RepairActor : Set where
  scopedButIneffective
  effectiveButIllegitimate
  legitimateAndEffective
  : RepairActor

data CanModify : RepairActor → Set where
  scopedCanModify : CanModify scopedButIneffective
  effectiveCanModify : CanModify effectiveButIllegitimate
  legitimateCanModify : CanModify legitimateAndEffective

data Attempted : RepairActor → Set where
  scopedAttempt : Attempted scopedButIneffective
  effectiveAttempt : Attempted effectiveButIllegitimate
  legitimateAttempt : Attempted legitimateAndEffective

data Effective : RepairActor → Set where
  effectiveWorked : Effective effectiveButIllegitimate
  legitimateWorked : Effective legitimateAndEffective

data CapabilityExpanded : RepairActor → Set where
  effectiveExpanded : CapabilityExpanded effectiveButIllegitimate
  legitimateExpanded : CapabilityExpanded legitimateAndEffective

canModifyDoesNotGuaranteeEffect :
  CanModify scopedButIneffective → Effective scopedButIneffective → ⊥
canModifyDoesNotGuaranteeEffect scopedCanModify ()

effectiveChangeDoesNotGiveLegitimacyEvidence :
  Effective effectiveButIllegitimate →
  Legitimacy.AdmittedLegitimacy Legitimacy.demoEvidence Legitimacy.effectiveRepairNoLegitimacy → ⊥
effectiveChangeDoesNotGiveLegitimacyEvidence effectiveWorked legitimacy =
  (λ ()) (Legitimacy.ruleWitness legitimacy)

record AuthorityRepairBoundary : Set where
  constructor authority-repair-boundary
  field
    scopedAuthorityGuaranteesAttempt : Bool
    scopedAuthorityGuaranteesAttemptIsFalse : scopedAuthorityGuaranteesAttempt ≡ false
    attemptedRepairGuaranteesEffect : Bool
    attemptedRepairGuaranteesEffectIsFalse : attemptedRepairGuaranteesEffect ≡ false
    effectiveRepairGuaranteesCapabilityExpansion : Bool
    effectiveRepairGuaranteesCapabilityExpansionIsFalse :
      effectiveRepairGuaranteesCapabilityExpansion ≡ false
    successfulMaterialChangeGuaranteesLegitimacy : Bool
    successfulMaterialChangeGuaranteesLegitimacyIsFalse :
      successfulMaterialChangeGuaranteesLegitimacy ≡ false

canonicalAuthorityRepairBoundary : AuthorityRepairBoundary
canonicalAuthorityRepairBoundary =
  authority-repair-boundary false refl false refl false refl false refl
