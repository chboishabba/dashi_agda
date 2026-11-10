module DASHI.Geometry.KakeyaLorentzSpatialSliceExact where

------------------------------------------------------------------------
-- ATTRIBUTION / SCOPE
-- Reuses the DASHI original integer hyperbolic carrier and its
-- pre-existing B4 flat-space receipt. This is a zero-time spatial-slice
-- *algebraic* bridge, not a continuum R^3 metric identification.
-- Kakeya geometry and the 3D dimension theorem are due to Wang--Zahl,
-- Guth--Wang--Zahl and their antecedents; none is established here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_)
open import Data.Vec using (Vec)

import DASHI.Geometry.Signature.HyperbolicFormZ as HFZ
import DASHI.Physics.Closure.MinkowskiLimitReceipt as Flat

spatialSliceAtZero : Vec ℤ 3 → Flat.MinkowskiCarrier
spatialSliceAtZero coordinates = record
  { tau = + 0
  ; sigma = coordinates
  }

spatialSliceCoordinates :
  ∀ coordinates →
  HFZ.sigma (spatialSliceAtZero coordinates) ≡ coordinates
spatialSliceCoordinates _ = refl

spatialSliceTime :
  ∀ coordinates →
  HFZ.tau (spatialSliceAtZero coordinates) ≡ + 0
spatialSliceTime _ = refl

-- The exact same quadratic expression used by DASHI's intrinsic B4
-- flat receipt, specialized to the time-zero spatial carrier.
-- Do not equate this integer lattice with EuclideanSpace ℝ (Fin 3)
-- until the separate completion, scale and measure adapters are proved.
spatialSliceMinkowskiExpression :
  ∀ coordinates →
  Flat.minkowskiQuadratic (spatialSliceAtZero coordinates)
  ≡ ((+ 1) * ((+ 0) * (+ 0))) -
    ((+ 1) * HFZ.sumSq coordinates)
spatialSliceMinkowskiExpression _ = refl

-- A genuine selected carrier/substitution, not the prototype-only
-- Signature31.sig31 witness.
spatialSliceFlatReceipt :
  ∀ coordinates →
  Flat.CarrierQuadraticIsMinkowski.quadraticForm
    Flat.minkowskiLimitReceipt (spatialSliceAtZero coordinates)
  ≡
  Flat.CarrierQuadraticIsMinkowski.minkowskiNorm
    Flat.minkowskiLimitReceipt (spatialSliceAtZero coordinates)
spatialSliceFlatReceipt coordinates =
  Flat.CarrierQuadraticIsMinkowski.exactEquality
    Flat.minkowskiLimitReceipt (spatialSliceAtZero coordinates)
