module DASHI.Ontology.ProgenitorParentDynamicAuthorityRegression where

open import DASHI.Core.Prelude using (false; true; _≡_; ⊥)

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Governance.DiachronicDelegatedAuthorityBoundary as GovernanceDiachronic
import DASHI.Ontology.ProgenitorParentProjectionFibre as ParentFibre
import DASHI.Ontology.ProgenitorParentObserverDynamicsBridge as ParentDynamics
import DASHI.Ontology.ProgenitorParentAuthorityRoutingNonfactorabilityExact as Routing
import DASHI.Ontology.ProgenitorParentObserverFutureSafetyExact as Future
import DASHI.Ontology.ProgenitorParentDiachronicAuthorityFibreExact as DiachronicParent
import DASHI.Ontology.ProgenitorParentResidualDynamicsExact as Residual

routingNonfactorabilityRegression :
  NonFactor.FactorsThrough
    ParentFibre.projectParentSlot
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
  GovernanceDiachronic.freshAuthorisationRequired
    GovernanceDiachronic.newDiscretionaryStep ≡ true
freshAuthorisationRegression =
  DiachronicParent.newParentDiscretionRequiresFreshAuthorisation

parentReopeningRegression :
  (carrier : ParentFibre.ParentCarrier) →
  Residual.reopenParentCarrier
    (ParentFibre.projectParentSlot carrier)
    (Residual.parentResidual carrier) ≡ carrier
parentReopeningRegression = Residual.reopenParentCarrierExact

legalResidualMotionRegression :
  Residual.parentResidual
    (ParentDynamics.finalizeLegalParenthood ParentDynamics.preFinalizationCarrier)
  ≡ Residual.parentResidual ParentDynamics.preFinalizationCarrier
  → ⊥
legalResidualMotionRegression = Residual.legalFinalizationMustMoveResidual
