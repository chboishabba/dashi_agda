module DASHI.Ontology.ProgenitorParentDiachronicAuthorityFibreExact where

open import DASHI.Core.Prelude using (Bool; true; false; _≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Governance.DiachronicDelegatedAuthorityBoundary as Diachronic

open import DASHI.Ontology.ProgenitorParentHyperfabric
open import DASHI.Ontology.ProgenitorParentProjectionFibre

------------------------------------------------------------------------
-- Parent/caregiver authority is diachronic and scope-indexed.
--
-- The parent relation and the authority relation are independent fibres. This
-- module reuses the existing delegated-authority kernel rather than encoding
-- revocation/current-will semantics again inside ParentRole.
------------------------------------------------------------------------

data ParentAuthorityScope : Set where
  careScope recordsScope medicalScope legalDecisionScope : ParentAuthorityScope

record ParentAuthoritySnapshot : Set where
  constructor parentAuthoritySnapshot
  field
    authorityCarrier : ParentCarrier
    authorityTime : Nat
    authorityScope : ParentAuthorityScope
    mandate : Diachronic.DelegatedMandate
    revocation : Diachronic.RevocationEvent
open ParentAuthoritySnapshot public

currentAuthorityActive : ParentAuthoritySnapshot → Bool
currentAuthorityActive snapshot =
  Diachronic.active (Diachronic.revokedMandate (revocation snapshot))

canonicalRevokedParentAuthority : ParentAuthoritySnapshot
canonicalRevokedParentAuthority =
  parentAuthoritySnapshot
    adoptiveCarrier
    10
    legalDecisionScope
    (Diachronic.revokedMandate Diachronic.canonicalRevocationEvent)
    Diachronic.canonicalRevocationEvent

parentRelationCanPersistAfterAuthorityRevocation :
  projectParentSlot (authorityCarrier canonicalRevokedParentAuthority) ≡ parentP8810
parentRelationCanPersistAfterAuthorityRevocation = refl

revokedParentAuthorityIsNotCurrent :
  currentAuthorityActive canonicalRevokedParentAuthority ≡ false
revokedParentAuthorityIsNotCurrent = refl

revocationPreservesHistoricalRecord :
  Diachronic.historicalErasure
    (revocation canonicalRevokedParentAuthority) ≡ false
revocationPreservesHistoricalRecord =
  Diachronic.canonicalRevocationPreservesHistory

historicalEvidenceCannotSelfRestoreParentAuthority :
  Diachronic.historicalEvidenceRestoresAuthority
    Diachronic.canonicalDiachronicAuthorityPromotionBoundary ≡ false
historicalEvidenceCannotSelfRestoreParentAuthority =
  Diachronic.canonicalHistoricalEvidenceRestoresAuthorityFalse

newParentDiscretionRequiresFreshAuthorisation :
  Diachronic.freshAuthorisationRequired
    Diachronic.newDiscretionaryStep ≡ true
newParentDiscretionRequiresFreshAuthorisation =
  Diachronic.newDiscretionaryStepRequiresFreshAuthorisation

unavoidableContinuationDoesNotCreateFreshAuthority :
  Diachronic.freshAuthorisationRequired
    Diachronic.unavoidableContinuationStep ≡ false
unavoidableContinuationDoesNotCreateFreshAuthority =
  Diachronic.unavoidableContinuationDoesNotRequireFreshStartAuthority

supportRoleCannotSelfAuthoriseOverride :
  Diachronic.supporterCannotSelfAuthoriseOverride
    Diachronic.canonicalSupportedDecisionConditions ≡ true
supportRoleCannotSelfAuthoriseOverride = refl

------------------------------------------------------------------------
-- Authority-at-time is not recoverable from the public parent edge.
------------------------------------------------------------------------

record ParentDiachronicAuthorityBoundary : Set where
  constructor parentDiachronicAuthorityBoundary
  field
    parentRelationMeansCurrentAuthority : Bool
    parentRelationMeansCurrentAuthorityIsFalse :
      parentRelationMeansCurrentAuthority ≡ false
    historicalEvidenceRestoresCurrentAuthority : Bool
    historicalEvidenceRestoresCurrentAuthorityIsFalse :
      historicalEvidenceRestoresCurrentAuthority ≡ false
    supportRoleSelfAuthorisesOverride : Bool
    supportRoleSelfAuthorisesOverrideIsFalse :
      supportRoleSelfAuthorisesOverride ≡ false
    newDiscretionAfterRevocationNeedsFreshAuthority : Bool
    newDiscretionAfterRevocationNeedsFreshAuthorityIsTrue :
      newDiscretionAfterRevocationNeedsFreshAuthority ≡ true

canonicalParentDiachronicAuthorityBoundary : ParentDiachronicAuthorityBoundary
canonicalParentDiachronicAuthorityBoundary =
  parentDiachronicAuthorityBoundary false refl false refl false refl true refl
