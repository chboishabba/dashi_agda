module DASHI.Interop.FactorisationSpineCrossDomainAdapterExact where

open import DASHI.Core.Prelude

import DASHI.Core.CoarseFineFabricCalculusExact as Coarse
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Core.FactorisationSpineCrosswalkExact as Crosswalk
import DASHI.Core.ActionCrossingBraidExact as Crossing
import DASHI.Law.SecurityRoutingComparatorHypervoxelExact as Security
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IK

------------------------------------------------------------------------
-- CROSS-DOMAIN ADAPTERS INTO THE SAME PROJECTION-COLLISION SPINE
--
-- These are exact carrier translations.  They do not identify the domains or
-- import any law/culture/provenance conclusion into another domain.
------------------------------------------------------------------------

actionCrossingProjectionCollision :
  ∀ {surface : Crossing.ActionCrossingSurface} →
  Crossing.SameEndpointDifferentProvenance surface →
  Coarse.ProjectionCollision
    (Crossing.endpoint surface)
    (Crossing.provenance surface)
actionCrossingProjectionCollision witness =
  Crosswalk.nonFactorabilityToProjectionCollision
    (NonFactor.nonFactorabilityWitness
      (Crossing.leftTrace witness)
      (Crossing.rightTrace witness)
      (Crossing.sameEndpoint witness)
      (Crossing.differentProvenance witness))

securityRoutingProjectionCollision :
  Coarse.ProjectionCollision
    Security.coarseSecurityObserver
    Security.routingTarget
securityRoutingProjectionCollision =
  Crosswalk.nonFactorabilityToProjectionCollision
    Security.coarseIntensityNonFactorability

indigenousPropositionProvenanceCollision :
  Coarse.ProjectionCollision
    IK.extractedProposition
    IK.carrierProvenance
indigenousPropositionProvenanceCollision =
  Crosswalk.nonFactorabilityToProjectionCollision
    (NonFactor.nonFactorabilityWitness
      IK.indigenousMedicinalStoryCarrier
      IK.scientificMedicinalPaperCarrier
      refl
      (λ ()))

------------------------------------------------------------------------
-- Return path: the generic repair theorem yields domain-local necessary
-- refinement obligations.  These do not say which refinement is sufficient;
-- only that any sufficient repair must separate the witnessed collision.
------------------------------------------------------------------------

securityRoutingRepairRequiresSeparation :
  ∀ {Refinement : Set}
    (refine : Security.SecurityRoutingHypervoxel → Refinement) →
  Repair.RefinementRepairs
    Security.coarseSecurityObserver
    refine
    Security.routingTarget →
  refine Security.syntheticProtectiveHigh ≡
    refine Security.syntheticCoerciveHigh →
  ⊥
securityRoutingRepairRequiresSeparation refine =
  Crosswalk.projectionCollisionRepairRequiresSeparation
    securityRoutingProjectionCollision

indigenousProvenanceRepairRequiresSeparation :
  ∀ {Refinement : Set}
    (refine : IK.KnowledgeCarrier → Refinement) →
  Repair.RefinementRepairs
    IK.extractedProposition
    refine
    IK.carrierProvenance →
  refine IK.indigenousMedicinalStoryCarrier ≡
    refine IK.scientificMedicinalPaperCarrier →
  ⊥
indigenousProvenanceRepairRequiresSeparation refine =
  Crosswalk.projectionCollisionRepairRequiresSeparation
    indigenousPropositionProvenanceCollision

record CrossDomainFactorisationAdapterBoundary : Set where
  constructor cross-domain-factorisation-adapter-boundary
  field
    actionCrossingUsesSharedProjectionSpine : Bool
    securityRoutingUsesSharedProjectionSpine : Bool
    indigenousProvenanceUsesSharedProjectionSpine : Bool
    sharedSpineReturnsNecessaryRepairObligations : Bool
    separatingWitnessAutomaticallyProvesGlobalSufficiency : Bool
    commonProjectionShapeIdentifiesDomains : Bool
    commonProjectionShapeImportsDomainAuthority : Bool

canonicalCrossDomainFactorisationAdapterBoundary :
  CrossDomainFactorisationAdapterBoundary
canonicalCrossDomainFactorisationAdapterBoundary =
  cross-domain-factorisation-adapter-boundary
    true true true true false false false
