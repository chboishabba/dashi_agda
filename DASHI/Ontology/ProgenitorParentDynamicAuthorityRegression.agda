module DASHI.Ontology.ProgenitorParentDynamicAuthorityRegression where

open import DASHI.Core.Prelude using (Bool; true; false; _≡_; refl; ⊥)

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.ProvenanceBearingQuotient as Provenance

import DASHI.Ontology.ProgenitorParentAuthorityRoutingNonfactorabilityExact as Routing
import DASHI.Ontology.ProgenitorParentObserverFutureSafetyExact as Future
import DASHI.Ontology.ProgenitorParentDiachronicAuthorityFibreExact as DiachronicParent
import DASHI.Ontology.ProgenitorParentResidualDynamicsExact as Residual

routingNonfactorabilityRegression :
  NonFactor.FactorsThrough
    DASHI.Ontology.ProgenitorParentProjectionFibre.projectParentSlot
    Routing.routeParentAuthority → ⊥
routingNonfactorabilityRegression =
  Routing.parentSlotInsufficiencyBlocksAuthorityRouting

authorityFutureSafetyRegression :
  Dynamic.DynamicConsumerSafety
    Future.parentDecisionSystem
    (Future.parentDecisionProject Future.authorityDecisionConsumer) → ⊥
authorityFutureSafetyRegression =
  Future.authorityDecisionProjectionIsNotDynamicallySafe

revokedAuthorityRegression :
  DiachronicParent.currentAuthorityActive
    DiachronicParent.canonicalRevokedParentAuthority ≡ false
revokedAuthorityRegression =
  DiachronicParent.revokedParentAuthorityIsNotCurrent

freshAuthorisationRegression :
  DASHI.Governance.DiachronicDelegatedAuthorityBoundary.freshAuthorisationRequired
    DASHI.Governance.DiachronicDelegatedAuthorityBoundary.newDiscretionaryStep ≡ true
freshAuthorisationRegression =
  DiachronicParent.newParentDiscretionRequiresFreshAuthorisation

parentReopeningRegression :
  (carrier : DASHI.Ontology.ProgenitorParentProjectionFibre.ParentCarrier) →
  Residual.reopenParentCarrier
    (DASHI.Ontology.ProgenitorParentProjectionFibre.projectParentSlot carrier)
    (Residual.parentResidual carrier) ≡ carrier
parentReopeningRegression = Residual.reopenParentCarrierExact

legalResidualMotionRegression :
  Residual.parentResidual
    (DASHI.Ontology.ProgenitorParentObserverDynamicsBridge.finalizeLegalParenthood
      DASHI.Ontology.ProgenitorParentObserverDynamicsBridge.preFinalizationCarrier)
  ≡ Residual.parentResidual
      DASHI.Ontology.ProgenitorParentObserverDynamicsBridge.preFinalizationCarrier
  → ⊥
legalResidualMotionRegression = Residual.legalFinalizationMustMoveResidual
