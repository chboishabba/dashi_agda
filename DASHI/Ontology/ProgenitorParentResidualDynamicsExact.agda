module DASHI.Ontology.ProgenitorParentResidualDynamicsExact where

open import DASHI.Core.Prelude using (Bool; true; false; _≡_; refl; cong; ⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Core.ProvenanceBearingQuotient as Provenance

open import DASHI.Ontology.ProgenitorParentHyperfabric
open import DASHI.Ontology.ProgenitorParentProjectionFibre
open import DASHI.Ontology.ProgenitorParentPNFPullbackLattice
open import DASHI.Ontology.ProgenitorParentObserverDynamicsBridge

------------------------------------------------------------------------
-- Exact parent reopening.
--
-- The public surface is the Wikidata slot.  The proof-relevant residual is the
-- full relation vector.  This is deliberately not a claim that the residual is
-- public/disclosable; it is the coordinate required for exact reopening.
------------------------------------------------------------------------

levelFromParentSlot : WikidataParentSlot → NodeLevel
levelFromParentSlot fatherP22 = individualLevel
levelFromParentSlot motherP25 = individualLevel
levelFromParentSlot parentP8810 = individualLevel
levelFromParentSlot hybridOfP1531 = lineageLevel

parentResidual : ParentCarrier → RelationVector
parentResidual = carrierRelation

reopenParentCarrier : WikidataParentSlot → RelationVector → ParentCarrier
reopenParentCarrier slot residual = parentCarrier (levelFromParentSlot slot) residual

reopenParentCarrierExact :
  (carrier : ParentCarrier) →
  reopenParentCarrier (projectParentSlot carrier) (parentResidual carrier) ≡ carrier
reopenParentCarrierExact (parentCarrier individualLevel relationValue) = refl
reopenParentCarrierExact (parentCarrier lineageLevel relationValue) = refl

parentProvenanceBearingQuotient :
  Provenance.ProvenanceBearingQuotient parentFibreRestrictionCore
parentProvenanceBearingQuotient =
  Provenance.provenanceBearingQuotient
    RelationVector
    parentResidual
    reopenParentCarrier
    reopenParentCarrierExact

------------------------------------------------------------------------
-- Exact reopening makes (surface,residual) separating.
------------------------------------------------------------------------

sameSurfaceAndResidualDetermineParentCarrier :
  ∀ {left right : ParentCarrier} →
  projectParentSlot left ≡ projectParentSlot right →
  parentResidual left ≡ parentResidual right →
  left ≡ right
sameSurfaceAndResidualDetermineParentCarrier {left} {right} sameSurface sameResidual =
  trans
    (sym (reopenParentCarrierExact left))
    (trans
      (cong
        (λ slotValue → reopenParentCarrier slotValue (parentResidual left))
        sameSurface)
      (trans
        (cong
          (λ residualValue → reopenParentCarrier (projectParentSlot right) residualValue)
          sameResidual)
        (reopenParentCarrierExact right)))

------------------------------------------------------------------------
-- Therefore every nontrivial hidden parent transition at fixed slot must move
-- the exact residual.  Legal finalisation gives the canonical witness.
------------------------------------------------------------------------

legalFinalizationMustMoveResidual :
  parentResidual (finalizeLegalParenthood preFinalizationCarrier) ≡
  parentResidual preFinalizationCarrier → ⊥
legalFinalizationMustMoveResidual sameResidual =
  finalizationActuallyChangesFineState
    (sameSurfaceAndResidualDetermineParentCarrier
      (finalizePreservesParentSlot preFinalizationCarrier)
      sameResidual)

disclosureChangeMustMoveResidual :
  parentResidual anonymousDonorCarrier ≡
  parentResidual anonymousDonorDisclosableCarrier → ⊥
disclosureChangeMustMoveResidual sameResidual =
  falseNotTrue
    (cong identityDisclosable sameResidual)

sameP8810SurfaceButResidualDisclosureMoves :
  projectParentSlot anonymousDonorCarrier ≡
    projectParentSlot anonymousDonorDisclosableCarrier
sameP8810SurfaceButResidualDisclosureMoves = refl

------------------------------------------------------------------------
-- Receipt motion remains semantically and normatively bounded: exact residual
-- retention is not permission to disclose or to promote it to world truth.
------------------------------------------------------------------------

parentResidualDoesNotSelfAuthoriseDisclosure :
  Provenance.ProjectionSemanticErasurePermission
    Provenance.projectionReceiptOnly → ⊥
parentResidualDoesNotSelfAuthoriseDisclosure =
  Provenance.projectionReceiptCannotEraseSemantics

record ParentResidualDynamicsBoundary : Set where
  constructor parentResidualDynamicsBoundary
  field
    surfacePlusResidualReopensExactly : Bool
    surfacePlusResidualReopensExactlyIsTrue :
      surfacePlusResidualReopensExactly ≡ true
    hiddenLegalMotionChangesResidual : Bool
    hiddenLegalMotionChangesResidualIsTrue :
      hiddenLegalMotionChangesResidual ≡ true
    hiddenDisclosureMotionChangesResidual : Bool
    hiddenDisclosureMotionChangesResidualIsTrue :
      hiddenDisclosureMotionChangesResidual ≡ true
    residualMotionGrantsDisclosureAuthority : Bool
    residualMotionGrantsDisclosureAuthorityIsFalse :
      residualMotionGrantsDisclosureAuthority ≡ false

canonicalParentResidualDynamicsBoundary : ParentResidualDynamicsBoundary
canonicalParentResidualDynamicsBoundary =
  parentResidualDynamicsBoundary true refl true refl true refl false refl
