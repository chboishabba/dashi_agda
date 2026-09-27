{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.SpacetimeMereologyBridgeExact where

open import Agda.Primitive using (Set₁)\nopen import Agda.Builtin.Bool using (Bool; false)\nopen import Agda.Builtin.Equality using (_≡_; refl)
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
    containmentSuppliesGluing : Bool
    containmentSuppliesGluingIsFalse :
      containmentSuppliesGluing ≡ false

    spatialOverlapSuppliesCompatibility : Bool
    spatialOverlapSuppliesCompatibilityIsFalse :
      spatialOverlapSuppliesCompatibility ≡ false

    mereologicalCarrierSuppliesCauchyEvolution : Bool
    mereologicalCarrierSuppliesCauchyEvolutionIsFalse :
      mereologicalCarrierSuppliesCauchyEvolution ≡ false

    mereologicalCarrierSuppliesGR : Bool
    mereologicalCarrierSuppliesGRIsFalse :
      mereologicalCarrierSuppliesGR ≡ false

canonicalSpacetimeMereologyBoundary : SpacetimeMereologyBoundary
canonicalSpacetimeMereologyBoundary = record
  { containmentSuppliesGluing = false
  ; containmentSuppliesGluingIsFalse = refl
  ; spatialOverlapSuppliesCompatibility = false
  ; spatialOverlapSuppliesCompatibilityIsFalse = refl
  ; mereologicalCarrierSuppliesCauchyEvolution = false
  ; mereologicalCarrierSuppliesCauchyEvolutionIsFalse = refl
  ; mereologicalCarrierSuppliesGR = false
  ; mereologicalCarrierSuppliesGRIsFalse = refl
  }
