{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologySpacetimePromotionExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Quantum.QuantumMereologyExact as QM
import DASHI.Quantum.EntanglementGeometryMereologyBridgeExact as EG
import DASHI.Physics.Closure.TemporalSheafProofObligations as Sheaf

------------------------------------------------------------------------
-- Spatial emergent geometry -> spacetime is an additional promotion seam.
------------------------------------------------------------------------

record QuantumMereologySpacetimePromotion
    (W : QM.BareQuantumWorld)
    (T : QM.TensorProductStructure W)
    (G : EG.FactorRelationGeometry W T) : Set₁ where
  field
    state : QM.State W
    spacetime : Sheaf.SpacetimeSheafObligation

    SameSpatialCarrier : Set
    sameSpatialCarrier : SameSpatialCarrier

    EntanglementDistanceAgreesWithSpatialGeometry : Set
    entanglementDistanceAgreesWithSpatialGeometry :
      EntanglementDistanceAgreesWithSpatialGeometry

    SpacetimeGluingPaid : Set
    spacetimeGluingPaid : SpacetimeGluingPaid

open QuantumMereologySpacetimePromotion public

record QuantumMereologySpacetimeBoundary : Set where
  field
    spatialGeometryAutomaticallySuppliesTime : Bool
    spatialGeometryAutomaticallySuppliesTimeIsFalse :
      spatialGeometryAutomaticallySuppliesTime ≡ false

    spatialGeometryAutomaticallySuppliesGluing : Bool
    spatialGeometryAutomaticallySuppliesGluingIsFalse :
      spatialGeometryAutomaticallySuppliesGluing ≡ false

    spatialGeometryAutomaticallySuppliesCauchyEvolution : Bool
    spatialGeometryAutomaticallySuppliesCauchyEvolutionIsFalse :
      spatialGeometryAutomaticallySuppliesCauchyEvolution ≡ false

    spatialGeometryAutomaticallySuppliesEinsteinDynamics : Bool
    spatialGeometryAutomaticallySuppliesEinsteinDynamicsIsFalse :
      spatialGeometryAutomaticallySuppliesEinsteinDynamics ≡ false

canonicalQuantumMereologySpacetimeBoundary :
  QuantumMereologySpacetimeBoundary
canonicalQuantumMereologySpacetimeBoundary = record
  { spatialGeometryAutomaticallySuppliesTime = false
  ; spatialGeometryAutomaticallySuppliesTimeIsFalse = refl
  ; spatialGeometryAutomaticallySuppliesGluing = false
  ; spatialGeometryAutomaticallySuppliesGluingIsFalse = refl
  ; spatialGeometryAutomaticallySuppliesCauchyEvolution = false
  ; spatialGeometryAutomaticallySuppliesCauchyEvolutionIsFalse = refl
  ; spatialGeometryAutomaticallySuppliesEinsteinDynamics = false
  ; spatialGeometryAutomaticallySuppliesEinsteinDynamicsIsFalse = refl
  }
