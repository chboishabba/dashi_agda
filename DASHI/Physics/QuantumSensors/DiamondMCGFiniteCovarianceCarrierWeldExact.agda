module DASHI.Physics.QuantumSensors.DiamondMCGFiniteCovarianceCarrierWeldExact where

------------------------------------------------------------------------
-- Phase P1: concrete reuse of the existing rational matrix inverse owner.
-- Source mathematics: classical finite matrix inversion / GLS (not new).
-- Repository owner: BalabanConstructiveRationalMatrixInverseExact.
-- Magnetic forward producer: DiamondMCGFiniteBridgeExact (finite mode only).
-- Units owner: DASHI.Physics.Units.SI (BIPM SI Brochure, 2026 revision).
-- Empirical source: Omar et al., Science Advances 12 (2026) eaeg5281.
--
-- This module proves that the certified inverse-covariance response solves
-- the covariance normal equation in every coordinate; it does not assume
-- that a measured PSD has been converted to the rational covariance matrix.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Mat
import DASHI.Physics.QuantumSensors.DiamondMCGFiniteBridgeExact as MCG
import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Units.SI as SI

record FiniteDiamondCovarianceModel (Index : Set) : Set₁ where
  field
    carrier : Mat.FiniteRationalCoordinates Index
    -- This is an exact, dimensionless rational representation of a
    -- frequency-bin covariance. Calibration defines the physical scale.
    covariance : Mat.RationalMatrix Index
    inverseCertificate :
      Mat.RationalMatrixInverseCertificate carrier covariance
    geometry : Index → MCG.FiniteModeMCG
    currentMode : V.Vector3

    -- Exact conversion from the model's rational magnetic field to
    -- calibrated physical magnetic quantities is NOT implicit.
    instrumentSource instrumentVersion : String
    physicalFrequency : SI.Quantity SI.Frequency SI.unitScale
    physicalFieldScale : SI.Quantity SI.MagneticFluxDensity SI.nanoScale
    physicalCovarianceIdentification : Set
    physicalCovarianceWitness : physicalCovarianceIdentification
open FiniteDiamondCovarianceModel public

-- This is the *same* cardiac current mode and per-sensor geometry as the
-- existing Fourier Biot-Savart finite producer, not a new field law.
cardiacArrayResponse :
  ∀ {Index} → FiniteDiamondCovarianceModel Index →
  Mat.RationalVector Index
cardiacArrayResponse model index =
  MCG.modelMCG (geometry model index) (currentMode model)

-- The inverse-covariance weighting is the exact old matrix owner's apply.
inverseCovarianceResponse :
  ∀ {Index} → (model : FiniteDiamondCovarianceModel Index) →
  Mat.RationalVector Index
inverseCovarianceResponse model =
  Mat.applyMatrix (carrier model)
    (Mat.inverseMatrix (inverseCertificate model))
    (cardiacArrayResponse model)

-- Genuine theorem, rather than a field postulating the desired result:
-- the covariance operator acts on the computed inverse-weighted cardiac
-- response and returns the original response at *every sensor*.
covarianceRecoversCardiacResponse :
  ∀ {Index} (model : FiniteDiamondCovarianceModel Index) (index : Index) →
  Mat.applyMatrix (carrier model) (covariance model)
    (inverseCovarianceResponse model) index
    ≡ cardiacArrayResponse model index
covarianceRecoversCardiacResponse model index =
  Mat.matrixInverseRightExact
    (inverseCertificate model)
    (cardiacArrayResponse model)
    index

-- The inverse-covariance transform is also a left inverse of the forward
-- covariance action. This can be used as the exact algebraic starting point
-- for the nontrivial C^{-1}-weighted matched-filter information theorem.
inverseRecoversCovarianceAppliedVector :
  ∀ {Index} (model : FiniteDiamondCovarianceModel Index)
    (vector : Mat.RationalVector Index) (index : Index) →
  Mat.applyMatrix (carrier model)
    (Mat.inverseMatrix (inverseCertificate model))
    (Mat.applyMatrix (carrier model) (covariance model) vector) index
    ≡ vector index
inverseRecoversCovarianceAppliedVector model vector index =
  Mat.matrixInverseLeftExact (inverseCertificate model) vector index
