{-# OPTIONS --safe #-}
module DASHI.Geometry.GielisOpticalTorqueCrossSIExact where

------------------------------------------------------------------------
-- ORIGINAL 2D wall-radiation force and signed angular moment in SI.
--
-- For finite ray hit position r=(x,y), incoming/outgoing unit directions
-- d_in=(ix,iy), d_out=(ox,oy), and reflected power fraction eta:
--   Δd = d_in - eta*d_out
--   z·(r×Δd) = x*(iy-eta*oy)-y*(ix-eta*ox).
--
-- Existing DASHI Hodge3 uses the 3D right-hand cross orientation.
-- This finite rational coordinate carrier has the same polynomial sign
-- convention, but DOES NOT claim an undocumented rational-to-axiomatic
-- real type equivalence.
--
-- Typed power P [W], inverse speed c^-1 [s/m], and signed lever arm
-- h=[m] multiply to the actual SI torque role N m.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as Ring

import DASHI.Geometry.GielisSIPerronOwnerWeldExact as SIWeld
import DASHI.Physics.Units.MechanicalDimensionExact as Mechanical
import DASHI.Physics.YangMills.YangMillsSIScalingEndpointExact as ExistingSI
import DASHI.Physics.Units.SI as SI
import DASHI.Physics.Foundations.R3HodgeCrossExact as Hodge

signedWallLever :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
signedWallLever x y ix iy ox oy eta =
  x * (iy - eta * oy) - y * (ix - eta * ox)

signedWallImpulseDirection :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
signedWallImpulseDirection x y ix iy ox oy eta =
  signedWallLever x y ix iy ox oy eta

rationalCrossZ :
  ℚ → ℚ → ℚ → ℚ → ℚ
rationalCrossZ x y fx fy = x * fy - y * fx

wallLeverIsCrossZ :
  ∀ x y ix iy ox oy eta →
  signedWallLever x y ix iy ox oy eta
  ≡ rationalCrossZ x y (ix - eta * ox) (iy - eta * oy)
wallLeverIsCrossZ x y ix iy ox oy eta = refl

crossAntisymmetry :
  ∀ x y fx fy →
  rationalCrossZ x y fx fy ≡ - (rationalCrossZ fx fy x y)
crossAntisymmetry x y fx fy = Ring.solve-∀ x y fx fy

noDeflectionNoImpulse :
  ∀ x y ix iy →
  signedWallLever x y ix iy ix iy 1ℚ ≡ 0ℚ
noDeflectionNoImpulse x y ix iy = Ring.solve-∀ x y ix iy

swapIncomingOutgoingReversesSignedLever :
  ∀ x y ix iy ox oy →
  signedWallLever x y ix iy ox oy 1ℚ
  ≡ - signedWallLever x y ox oy ix iy 1ℚ
swapIncomingOutgoingReversesSignedLever x y ix iy ox oy =
  Ring.solve-∀ x y ix iy ox oy

rotatePositionAndRayPiPreservesSignedLever :
  ∀ x y ix iy ox oy eta →
  signedWallLever
    (- x) (- y) (- ix) (- iy) (- ox) (- oy) eta
  ≡ signedWallLever x y ix iy ox oy eta
rotatePositionAndRayPiPreservesSignedLever x y ix iy ox oy eta =
  Ring.solve-∀ x y ix iy ox oy eta

-- The selected signed geometric lever arm has mechanical LENGTH
-- dimensions. It need not be positive (and may vanish by symmetry).
modelWallTorque :
  ℚ → ℚ →
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ →
  Mechanical.Quantity ℚ Mechanical.energyDimension
modelWallTorque power inverseC x y ix iy ox oy eta =
  SIWeld.modelOpticalTorque
    (Mechanical.quantity power)
    (Mechanical.quantity inverseC)
    (Mechanical.quantity
      (signedWallLever x y ix iy ox oy eta))

modelWallTorqueMagnitude :
  ∀ power inverseC x y ix iy ox oy eta →
  Mechanical.magnitude
    (modelWallTorque power inverseC x y ix iy ox oy eta)
  ≡ (power * inverseC)
      * signedWallLever x y ix iy ox oy eta
modelWallTorqueMagnitude power inverseC x y ix iy ox oy eta =
  SIWeld.modelOpticalTorqueHasActualMagnitude
    power inverseC
    (signedWallLever x y ix iy ox oy eta)

modelWallTorqueSI :
  ℚ → ℚ →
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ →
  ExistingSI.SIIndexedQuantity ℚ SI.Energy
modelWallTorqueSI power inverseC x y ix iy ox oy eta =
  ExistingSI.mechanicalQuantityToSI
    (modelWallTorque power inverseC x y ix iy ox oy eta)

modelWallTorqueSIMagnitude :
  ∀ power inverseC x y ix iy ox oy eta →
  ExistingSI.magnitude
    (modelWallTorqueSI power inverseC x y ix iy ox oy eta)
  ≡ (power * inverseC)
      * signedWallLever x y ix iy ox oy eta
modelWallTorqueSIMagnitude power inverseC x y ix iy ox oy eta =
  SIWeld.modelOpticalTorqueSIMagnitude
    power inverseC
    (signedWallLever x y ix iy ox oy eta)

-- Existing 3D Hodge orientation is the donor, but its underlying
-- RealAnalysisAxioms carrier is NOT silently identified with ℚ.
existingHodgeCrossConvention : ∀ r f →
  Hodge.hodgeStar3 (Hodge.wedge3 r f) ≡ Hodge.cross3 r f
existingHodgeCrossConvention = Hodge.hodgeWedgeEqualsCross
