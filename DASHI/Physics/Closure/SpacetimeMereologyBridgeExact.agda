{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.SpacetimeMereologyBridgeExact where

open import Agda.Primitive using (Set₁)
import DASHI.Physics.Closure.TemporalSheafProofObligations as Sheaf

------------------------------------------------------------------------
-- THE MEREOLOGICAL FRAGMENT OF A SPACETIME-SHEAF OBLIGATION
--
-- This deliberately extracts only containment and spatial overlap.
-- Compatibility, gluing, global sections, Cauchy evolution, and topology
-- change remain separate obligations and are not manufactured by mereology.
------------------------------------------------------------------------

record SpatialMereologyFragment : Set₁ where
  field
    Space : Set

    partOf :
      Space → Space → Set

    overlap :
      Space → Space → Set

open SpatialMereologyFragment public

fromSpacetimeSheafObligation :
  Sheaf.SpacetimeSheafObligation →
  SpatialMereologyFragment
fromSpacetimeSheafObligation spacetime = record
  { Space = Sheaf.SpacetimeSheafObligation.Space spacetime
  ; partOf = Sheaf.SpacetimeSheafObligation._⊑space_ spacetime
  ; overlap = Sheaf.SpacetimeSheafObligation.spatialOverlap spacetime
  }

record SpacetimeMereologyBoundary : Set where
  field
    containmentDoesNotSupplyGluing : Set
    spatialOverlapDoesNotSupplyCompatibility : Set
    mereologicalCarrierDoesNotSupplyCauchyEvolution : Set
    mereologicalCarrierDoesNotSupplyGR : Set

------------------------------------------------------------------------
-- The boundary is intentionally an obligation surface: a consumer that wants
-- any of the stronger readings must provide the corresponding witness.
------------------------------------------------------------------------
