module DASHI.Ontology.ProgenitorParentAuthorityRoutingNonfactorabilityExact where

open import DASHI.Core.Prelude using (Bool; true; false; _≡_; refl; cong; ⊥)
import DASHI.Core.IntersectionalNonFactorability as NonFactor

open import DASHI.Ontology.ProgenitorParentHyperfabric
open import DASHI.Ontology.ProgenitorParentProjectionFibre

------------------------------------------------------------------------
-- A Wikidata parent slot is not a sufficient carrier for authority routing.
--
-- This is deliberately stronger than "the slot loses semantics": it proves
-- that no interpretation on the coarse slot can reproduce an action-routing
-- function which distinguishes two fine parent states in the same slot fibre.
------------------------------------------------------------------------

data ParentAuthorityRoute : Set where
  noParentalAuthorityRoute legalParentDecisionRoute : ParentAuthorityRoute

routeParentAuthority : ParentCarrier → ParentAuthorityRoute
routeParentAuthority carrier with legalParent (carrierRelation carrier)
... | false = noParentalAuthorityRoute
... | true  = legalParentDecisionRoute

anonymousDonorHasNoLegalParentRoute :
  routeParentAuthority anonymousDonorCarrier ≡ noParentalAuthorityRoute
anonymousDonorHasNoLegalParentRoute = refl

adoptiveParentHasLegalDecisionRoute :
  routeParentAuthority adoptiveCarrier ≡ legalParentDecisionRoute
adoptiveParentHasLegalDecisionRoute = refl

routesDiffer :
  routeParentAuthority anonymousDonorCarrier ≡
  routeParentAuthority adoptiveCarrier → ⊥
routesDiffer ()

p8810AuthorityRoutingNonFactorability :
  NonFactor.NonFactorabilityWitness projectParentSlot routeParentAuthority
p8810AuthorityRoutingNonFactorability =
  NonFactor.nonFactorabilityWitness
    anonymousDonorCarrier
    adoptiveCarrier
    refl
    routesDiffer

parentSlotInsufficiencyBlocksAuthorityRouting :
  NonFactor.FactorsThrough projectParentSlot routeParentAuthority → ⊥
parentSlotInsufficiencyBlocksAuthorityRouting =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    p8810AuthorityRoutingNonFactorability

------------------------------------------------------------------------
-- The same public relation may therefore support different legitimate routes.
-- No re-labelling or reweighting *inside the P8810 carrier* repairs this loss;
-- the routing carrier itself has to retain the relevant fine coordinate.
------------------------------------------------------------------------

record ParentAuthorityRoutingBoundary : Set where
  constructor parentAuthorityRoutingBoundary
  field
    samePublicSlotCanRequireDifferentRoute : Bool
    samePublicSlotCanRequireDifferentRouteIsTrue :
      samePublicSlotCanRequireDifferentRoute ≡ true
    coarseSlotCanRecoverAuthorityRoute : Bool
    coarseSlotCanRecoverAuthorityRouteIsFalse :
      coarseSlotCanRecoverAuthorityRoute ≡ false

canonicalParentAuthorityRoutingBoundary : ParentAuthorityRoutingBoundary
canonicalParentAuthorityRoutingBoundary =
  parentAuthorityRoutingBoundary true refl false refl
