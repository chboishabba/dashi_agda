module DASHI.Empirical.DarkDimensionSharedBAOObservableExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Empirical.DarkDimensionEmpiricalDiscriminationExact as Discrimination
import DASHI.Empirical.DarkDimensionModelObservableMatrixExact as Matrix
import DASHI.Empirical.GRQuantumPredictionProtocol as Prediction
import DASHI.Physics.Closure.DarkDimensionStringPromotionBoundaryExact as DarkDimension

------------------------------------------------------------------------
-- SHARED DESI BAO OBSERVABLE SEAM
--
-- The model-observable matrix correctly blocks subtraction of unlike internal
-- coordinates such as c', R_perp and A_D.  Both competing phenomenological
-- lanes nevertheless meet at the DESI BAO distance surface:
--
--   transverse : D_M(z) / r_d
--   radial     : D_H(z) / r_d
--
-- Bedroya-Obied-Vafa-Wu fit DESI DR2 BAO measurements on this surface.
-- Garny-Niedermann-Sloth model how a nearby DAO biases the inferred values on
-- the same surface.  This owner pays only that same-observable identity.
-- It does not manufacture model predictions, covariance, a likelihood, or a
-- future locked separation on either coordinate.
------------------------------------------------------------------------

data SharedBAOObservable : Set where
  transverseDMOverRd : SharedBAOObservable
  radialDHOverRd : SharedBAOObservable

record BAOCoordinateDefinition (observable : SharedBAOObservable) : Set where
  constructor baoCoordinateDefinition
  field
    numerator : String
    denominator : String
    interpretation : String
    dimensionlessCoordinate : Bool

open BAOCoordinateDefinition public

transverseDefinition : BAOCoordinateDefinition transverseDMOverRd
transverseDefinition =
  baoCoordinateDefinition
    "D_M(z)"
    "r_d"
    "transverse comoving distance divided by the BAO drag horizon"
    true

radialDefinition : BAOCoordinateDefinition radialDHOverRd
radialDefinition =
  baoCoordinateDefinition
    "D_H(z)"
    "r_d"
    "line-of-sight Hubble distance divided by the BAO drag horizon"
    true

------------------------------------------------------------------------
-- Source-paid model -> observable projections.
------------------------------------------------------------------------

record ModelBAOProjection
    (model : Matrix.ModelKind)
    (observable : SharedBAOObservable) : Set where
  constructor modelBAOProjection
  field
    source : Source.AttributedSource
    modelMapsToObservable : Bool
    lockedNumericalPredictionOnObservable : Bool
    sourceScope : String

open ModelBAOProjection public

darkDimensionTransverseProjection :
  ModelBAOProjection Matrix.darkDimensionModel transverseDMOverRd
darkDimensionTransverseProjection =
  modelBAOProjection
    DarkDimension.bedroyaObiedVafaWu2026
    true
    false
    "Bedroya-Obied-Vafa-Wu use DESI DR2 BAO transverse-distance measurements; this source admission does not freeze a future D_M/r_d prediction"

darkDimensionRadialProjection :
  ModelBAOProjection Matrix.darkDimensionModel radialDHOverRd
darkDimensionRadialProjection =
  modelBAOProjection
    DarkDimension.bedroyaObiedVafaWu2026
    true
    false
    "Bedroya-Obied-Vafa-Wu use DESI DR2 BAO line-of-sight distance measurements; this source admission does not freeze a future D_H/r_d prediction"

daoTransverseProjection :
  ModelBAOProjection Matrix.darkAcousticOscillationModel transverseDMOverRd
daoTransverseProjection =
  modelBAOProjection
    Discrimination.darkAcousticOscillationSource
    true
    false
    "Garny-Niedermann-Sloth derive a DAO-induced apparent shift in the transverse BAO distance parameter; no future numerical D_M/r_d prediction is locked here"

daoRadialProjection :
  ModelBAOProjection Matrix.darkAcousticOscillationModel radialDHOverRd
daoRadialProjection =
  modelBAOProjection
    Discrimination.darkAcousticOscillationSource
    true
    false
    "Garny-Niedermann-Sloth derive a DAO-induced apparent shift in the radial BAO distance parameter; no future numerical D_H/r_d prediction is locked here"

------------------------------------------------------------------------
-- Same observable != same mechanism.
------------------------------------------------------------------------

data SameObservableImpliesSameMechanism : Set where

sameObservableDoesNotMeanSameMechanism :
  SameObservableImpliesSameMechanism → ⊥
sameObservableDoesNotMeanSameMechanism ()

------------------------------------------------------------------------
-- Status: the common carrier is now identified, while the actual head-to-head
-- numerical forecast remains unpaid on both shared coordinates.
------------------------------------------------------------------------

record SharedBAOStatus : Set where
  constructor sharedBAOStatus
  field
    darkDimensionMapsToTransverse : Bool
    darkDimensionMapsToRadial : Bool
    daoMapsToTransverse : Bool
    daoMapsToRadial : Bool
    sharedObservableIdentityEstablished : Bool
    darkDimensionTransversePredictionLocked : Bool
    darkDimensionRadialPredictionLocked : Bool
    daoTransversePredictionLocked : Bool
    daoRadialPredictionLocked : Bool
    sharedObservableNumericalSeparationLocked : Bool

open SharedBAOStatus public

canonicalSharedBAOStatus : SharedBAOStatus
canonicalSharedBAOStatus =
  sharedBAOStatus
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false

sharedObservableIdentityPaid :
  sharedObservableIdentityEstablished canonicalSharedBAOStatus ≡ true
sharedObservableIdentityPaid = refl

sharedObservableNumericalPredictionsStillOpen :
  sharedObservableNumericalSeparationLocked canonicalSharedBAOStatus ≡ false
sharedObservableNumericalPredictionsStillOpen = refl

------------------------------------------------------------------------
-- Promotion firewall: common observable identity is necessary for comparison,
-- but it is not a DASHI-derived QuantitativeFalsifiablePrediction.
------------------------------------------------------------------------

sharedObservableDoesNotPayQuantitativePrediction :
  Prediction.quantitativePredictionDerived
    Prediction.canonicalPredictionBoundary
  ≡ false
sharedObservableDoesNotPayQuantitativePrediction =
  Prediction.quantitativePredictionDerivedIsFalse
    Prediction.canonicalPredictionBoundary

bedroyaDOI : String
bedroyaDOI = "10.1103/1rsq-cv2m"

daoDOI : String
daoDOI = "10.1103/y31p-9g5k"
