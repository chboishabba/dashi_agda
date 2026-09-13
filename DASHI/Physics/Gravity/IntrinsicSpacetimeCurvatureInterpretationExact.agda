module DASHI.Physics.Gravity.IntrinsicSpacetimeCurvatureInterpretationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Laws.SpacetimeMechanicsLaws as Mechanics
import DASHI.Physics.Gravity.RelativityOpticalKernelBridge as Relativity
import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as Emergence

------------------------------------------------------------------------
-- Interpretation owner for the standard rubber-sheet analogy and the
-- weak-field free-fall explanation.
--
-- This module does not introduce another geometry ontology.  It reuses the
-- existing manifold/metric/connection/curvature/geodesic surfaces and records
-- which popular explanatory identifications are WrongType.
------------------------------------------------------------------------

record IntrinsicCurvatureInterpretationBoundary : Set where
  field
    rubberSheetEmbeddingIsNotIntrinsicLorentzianCurvature : Bool
    rubberSheetEmbeddingIsNotIntrinsicLorentzianCurvatureIsTrue :
      rubberSheetEmbeddingIsNotIntrinsicLorentzianCurvature ≡ true

    externalDownwardGravityIsNotGRSourceMechanism : Bool
    externalDownwardGravityIsNotGRSourceMechanismIsTrue :
      externalDownwardGravityIsNotGRSourceMechanism ≡ true

    extraSpatialEmbeddingDimensionNotRequired : Bool
    extraSpatialEmbeddingDimensionNotRequiredIsTrue :
      extraSpatialEmbeddingDimensionNotRequired ≡ true

    spatialCurvatureIsNotFullSpacetimeCurvature : Bool
    spatialCurvatureIsNotFullSpacetimeCurvatureIsTrue :
      spatialCurvatureIsNotFullSpacetimeCurvature ≡ true

    freeFallUsesTimelikeGeodesicLimit : Bool
    freeFallUsesTimelikeGeodesicLimitIsTrue :
      freeFallUsesTimelikeGeodesicLimit ≡ true

    weakFieldTemporalMetricContribution : String

    timeCurvesIntoSpacePhraseIsNotInvariantGRStatement : Bool
    timeCurvesIntoSpacePhraseIsNotInvariantGRStatementIsTrue :
      timeCurvesIntoSpacePhraseIsNotInvariantGRStatement ≡ true

open IntrinsicCurvatureInterpretationBoundary public

canonicalIntrinsicCurvatureInterpretationBoundary :
  IntrinsicCurvatureInterpretationBoundary
canonicalIntrinsicCurvatureInterpretationBoundary = record
  { rubberSheetEmbeddingIsNotIntrinsicLorentzianCurvature = true
  ; rubberSheetEmbeddingIsNotIntrinsicLorentzianCurvatureIsTrue = refl
  ; externalDownwardGravityIsNotGRSourceMechanism = true
  ; externalDownwardGravityIsNotGRSourceMechanismIsTrue = refl
  ; extraSpatialEmbeddingDimensionNotRequired = true
  ; extraSpatialEmbeddingDimensionNotRequiredIsTrue = refl
  ; spatialCurvatureIsNotFullSpacetimeCurvature = true
  ; spatialCurvatureIsNotFullSpacetimeCurvatureIsTrue = refl
  ; freeFallUsesTimelikeGeodesicLimit = true
  ; freeFallUsesTimelikeGeodesicLimitIsTrue = refl
  ; weakFieldTemporalMetricContribution =
      "in the slow-motion weak-field limit, Newtonian gravitational acceleration is encoded primarily through spatial variation of the temporal metric component g_00; the invariant GR carrier remains the full Lorentzian metric/connection/curvature, not a literal bending of time into space"
  ; timeCurvesIntoSpacePhraseIsNotInvariantGRStatement = true
  ; timeCurvesIntoSpacePhraseIsNotInvariantGRStatementIsTrue = refl
  }

------------------------------------------------------------------------
-- Repo-native reuse witnesses.
------------------------------------------------------------------------

existingDifferentialGeometricDynamics : Set₁
existingDifferentialGeometricDynamics = Mechanics.DifferentialGeometricDynamics

existingRelativityKernelClosure : Set
existingRelativityKernelClosure = Relativity.RelativityOpticalKernelClosure

existingGeometryEmergenceBoundary : Set
existingGeometryEmergenceBoundary = Emergence.KernelGeometryBoundary

record CurvatureInterpretationReceipt : Set where
  field
    intrinsicGeometryUsesExistingMetricConnectionCurvature : Bool
    intrinsicGeometryUsesExistingMetricConnectionCurvatureIsTrue :
      intrinsicGeometryUsesExistingMetricConnectionCurvature ≡ true

    interpretationOwnerDerivesEinsteinDynamics : Bool
    interpretationOwnerDerivesEinsteinDynamicsIsFalse :
      interpretationOwnerDerivesEinsteinDynamics ≡ false

open CurvatureInterpretationReceipt public

canonicalCurvatureInterpretationReceipt : CurvatureInterpretationReceipt
canonicalCurvatureInterpretationReceipt = record
  { intrinsicGeometryUsesExistingMetricConnectionCurvature = true
  ; intrinsicGeometryUsesExistingMetricConnectionCurvatureIsTrue = refl
  ; interpretationOwnerDerivesEinsteinDynamics = false
  ; interpretationOwnerDerivesEinsteinDynamicsIsFalse = refl
  }
