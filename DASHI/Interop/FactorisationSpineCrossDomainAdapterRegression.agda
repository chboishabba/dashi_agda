module DASHI.Interop.FactorisationSpineCrossDomainAdapterRegression where

open import DASHI.Core.Prelude

import DASHI.Core.CoarseFineFabricCalculusExact as Coarse
import DASHI.Core.ActionCrossingBraidExact as Crossing
import DASHI.Law.SecurityRoutingComparatorHypervoxelExact as Security
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IK
import DASHI.Interop.FactorisationSpineCrossDomainAdapterExact as Adapter

securityCollision :
  Coarse.ProjectionCollision
    Security.coarseSecurityObserver
    Security.routingTarget
securityCollision = Adapter.securityRoutingProjectionCollision

indigenousCollision :
  Coarse.ProjectionCollision
    IK.extractedProposition
    IK.carrierProvenance
indigenousCollision = Adapter.indigenousPropositionProvenanceCollision

actionCrossingAdapter :
  ∀ {surface : Crossing.ActionCrossingSurface} →
  Crossing.SameEndpointDifferentProvenance surface →
  Coarse.ProjectionCollision
    (Crossing.endpoint surface)
    (Crossing.provenance surface)
actionCrossingAdapter = Adapter.actionCrossingProjectionCollision
