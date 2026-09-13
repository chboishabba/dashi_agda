module DASHI.Core.NDimProjectionLossAdapterExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.NDimParetoHyperfabricExact as NDim

------------------------------------------------------------------------
-- NDIM AXIS RESTRICTION -> PROJECTION-LOSS BOUNDARY
--
-- NDim already proves full dominance implies projected dominance.  This adapter
-- deliberately does not fabricate the converse or a concrete collision witness.
------------------------------------------------------------------------

record NDimProjectionBoundaryAdapter : Set where
  constructor ndimProjectionBoundaryAdapter
  field
    fullDominanceProjects : Bool
    projectedDominanceRecoversFullAutomatically : Bool
    omittedAxesAreIrrelevantToEveryConsumer : Bool
    dimensionEqualsProjectedStateCount : Bool

nDimProjectionBoundaryAdapter : NDimProjectionBoundaryAdapter
nDimProjectionBoundaryAdapter =
  ndimProjectionBoundaryAdapter true false false false

fullDominanceProjectsIsTrue :
  NDimProjectionBoundaryAdapter.fullDominanceProjects
    nDimProjectionBoundaryAdapter ≡ true
fullDominanceProjectsIsTrue = refl

projectedDominanceDoesNotRecoverFullAutomatically :
  NDimProjectionBoundaryAdapter.projectedDominanceRecoversFullAutomatically
    nDimProjectionBoundaryAdapter ≡ false
projectedDominanceDoesNotRecoverFullAutomatically = refl

existingNDimBoundary : NDim.NDimParetoHyperfabricBoundary
existingNDimBoundary = NDim.canonicalNDimParetoHyperfabricBoundary
