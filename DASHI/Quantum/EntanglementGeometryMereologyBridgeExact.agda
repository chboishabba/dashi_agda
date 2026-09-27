{-# OPTIONS --safe #-}
module DASHI.Quantum.EntanglementGeometryMereologyBridgeExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Set₁)

import DASHI.Quantum.QuantumMereologyExact as QM

------------------------------------------------------------------------
-- FACTORISATION -> RELATIONAL GRAPH -> DISTANCE -> SPATIAL GEOMETRY
--
-- This is a typed dependency chain, not a derivation of geometry from a bare
-- Hilbert carrier.  The information/metric and geometric-realisation laws are
-- explicit premises.
------------------------------------------------------------------------

record FactorRelationGeometry
    (W : QM.BareQuantumWorld)
    (T : QM.TensorProductStructure W) : Set₁ where
  field
    Weight Distance Geometry : Set

    pairWeight :
      QM.State W →
      QM.Subsystem T →
      QM.Subsystem T →
      Weight

    distanceFromWeight :
      Weight → Distance

    geometryFromDistances :
      (QM.Subsystem T → QM.Subsystem T → Distance) → Geometry

open FactorRelationGeometry public

emergentDistance :
  ∀ {W T} →
  (G : FactorRelationGeometry W T) →
  QM.State W →
  QM.Subsystem T →
  QM.Subsystem T →
  Distance G
emergentDistance G state left right =
  distanceFromWeight G (pairWeight G state left right)

emergentGeometry :
  ∀ {W T} →
  (G : FactorRelationGeometry W T) →
  QM.State W →
  Geometry G
emergentGeometry G state =
  geometryFromDistances G (emergentDistance G state)

------------------------------------------------------------------------
-- Perturbation / curvature-response socket.
-- A spatial Einstein-analogue result must be supplied explicitly.
------------------------------------------------------------------------

record EntanglementCurvatureResponse
    {W : QM.BareQuantumWorld}
    {T : QM.TensorProductStructure W}
    (G : FactorRelationGeometry W T) : Set₁ where
  field
    Perturbation CurvatureResponse : Set

    perturbState :
      Perturbation → QM.State W → QM.State W

    curvatureResponse :
      Perturbation → QM.State W → CurvatureResponse

    SpatialEinsteinAnalogue : Set
    spatialEinsteinAnalogue : SpatialEinsteinAnalogue

open EntanglementCurvatureResponse public

record EntanglementGeometryBoundary : Set where
  field
    entanglementWithoutTPSDefinesDistance : Bool
    entanglementWithoutTPSDefinesDistanceIsFalse :
      entanglementWithoutTPSDefinesDistance ≡ false

    TPSWithoutPairRelationDefinesGeometry : Bool
    TPSWithoutPairRelationDefinesGeometryIsFalse :
      TPSWithoutPairRelationDefinesGeometry ≡ false

    spatialGeometryIsFullSpacetime : Bool
    spatialGeometryIsFullSpacetimeIsFalse :
      spatialGeometryIsFullSpacetime ≡ false

    spatialEinsteinAnalogueIsFullGR : Bool
    spatialEinsteinAnalogueIsFullGRIsFalse :
      spatialEinsteinAnalogueIsFullGR ≡ false

canonicalEntanglementGeometryBoundary : EntanglementGeometryBoundary
canonicalEntanglementGeometryBoundary = record
  { entanglementWithoutTPSDefinesDistance = false
  ; entanglementWithoutTPSDefinesDistanceIsFalse = refl
  ; TPSWithoutPairRelationDefinesGeometry = false
  ; TPSWithoutPairRelationDefinesGeometryIsFalse = refl
  ; spatialGeometryIsFullSpacetime = false
  ; spatialGeometryIsFullSpacetimeIsFalse = refl
  ; spatialEinsteinAnalogueIsFullGR = false
  ; spatialEinsteinAnalogueIsFullGRIsFalse = refl
  }
