module DASHI.Physics.Closure.NSTriadKNHHGoodOrderZeroKineticCompensationNoGoRound42Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: J. Thomas Beale; Tosio Kato; Andrew Majda.
-- Title: "Remarks on the Breakdown of Smooth Solutions for the 3-D Euler
-- Equations".
-- Communications in Mathematical Physics 94 (1984), 61--66.
-- DOI: 10.1007/BF01240221.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- The companion Round-42 no-go proves that bare kinetic energy cannot bound
-- one of the literal vorticity amplitude squares in
--
--   W(a,b)=a^2 b^4:
--
--   |omega_k|^2 = |k|^2 |u_k|^2.
--
-- A possible escape would be to hope that the HH-good strain operator itself
-- returns the missing inverse derivative.  Round 40 already proves that this
-- is impossible at the multiplier level: the literal strain multiplier is
-- order zero,
--
--   S_{r k}(omega) = S_k(omega).
--
-- This file puts that fact beside the exact Biot--Savart scaling on the same
-- rational scaled projection mode.  For transverse fixed vorticity omega,
--
--   |B_{r k} omega|^2 = r^-2 |B_k omega|^2,
--
-- while
--
--   S_{r k}(omega) = S_k(omega).
--
-- Therefore the shell-invariant strain multiplier does not contain the
-- r^-2 compensation needed to turn a vorticity amplitude square into bare
-- kinetic energy.  Any viable HH-good repair using kinetic E0 must recover the
-- inverse derivative *before or outside* the already-absolute-valued order-zero
-- strain-kernel bound (for example through a cancellation, a different
-- weighted resource, or a time-localized estimate).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNFourierBiotSavartExact as BS
import DASHI.Physics.Closure.NSTriadKNFourierStrainMultiplierRound38Exact as Strain
import DASHI.Physics.Closure.NSTriadKNFourierStrainScaleInvariantRound40Exact as Scale
import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold

------------------------------------------------------------------------
-- Scaling a Fourier mode preserves transversality of a fixed vorticity vector.
------------------------------------------------------------------------

dotScaleLeft :
  (scalar : ℚ) (left right : V.Vector3) →
  V.dot (V.scale scalar left) right ≡ scalar * V.dot left right
dotScaleLeft scalar left right =
  trans
    (V.dotCommutative (V.scale scalar left) right)
    (trans
      (V.dotScaleRight right left scalar)
      (cong (scalar *_) (V.dotCommutative right left)))

scaledTransverse :
  (scale : Threshold.PositiveThreshold) →
  (modeData : V.ProjectionMode) →
  (omega : V.Vector3) →
  V.dot (V.mode modeData) omega ≡ 0ℚ →
  V.dot (V.mode (Scale.scaledProjectionMode scale modeData)) omega ≡ 0ℚ
scaledTransverse scale modeData omega transverse =
  trans
    (cong (λ mode → V.dot mode omega)
      (Scale.scaledProjectionModeMode scale modeData))
    (trans
      (dotScaleLeft (Threshold.threshold scale) (V.mode modeData) omega)
      (trans
        (cong (Threshold.threshold scale *_) transverse)
        (solve (Threshold.threshold scale ∷ []))))

------------------------------------------------------------------------
-- Exact Biot--Savart norm scaling on the same scaled mode.
------------------------------------------------------------------------

scaledBiotSavartNormSquared :
  (scale : Threshold.PositiveThreshold) →
  (modeData : V.ProjectionMode) →
  (omega : V.Vector3) →
  (transverse : V.dot (V.mode modeData) omega ≡ 0ℚ) →
  V.normSquared
      (BS.biotSavart (Scale.scaledProjectionMode scale modeData) omega)
  ≡
  (Threshold.thresholdInverse scale * Threshold.thresholdInverse scale)
    * V.normSquared (BS.biotSavart modeData omega)
scaledBiotSavartNormSquared scale modeData omega transverse =
  let
    rinv = Threshold.thresholdInverse scale
    inv = V.inverseNormSquared modeData
    omegaNorm = V.normSquared omega

    scaledGain =
      BS.biotSavartNormGainSquared
        (Scale.scaledProjectionMode scale modeData)
        omega
        (scaledTransverse scale modeData omega transverse)

    originalGain = BS.biotSavartNormGainSquared modeData omega transverse

    exposeScaledInverse :
      V.inverseNormSquared (Scale.scaledProjectionMode scale modeData)
        * omegaNorm
      ≡ (inv * rinv * rinv) * omegaNorm
    exposeScaledInverse =
      cong (_* omegaNorm) (Scale.scaledProjectionModeInverse scale modeData)

    regroup :
      (inv * rinv * rinv) * omegaNorm
      ≡ (rinv * rinv) * (inv * omegaNorm)
    regroup = solve (inv ∷ rinv ∷ omegaNorm ∷ [])
  in
  trans scaledGain
    (trans exposeScaledInverse
      (trans regroup
        (cong ((rinv * rinv) *_) (sym originalGain))))

------------------------------------------------------------------------
-- The contrast: velocity gains r^-1, strain is exactly order zero.
------------------------------------------------------------------------

scaledStrainMultiplierUnchanged :
  (scale : Threshold.PositiveThreshold) →
  (modeData : V.ProjectionMode) →
  (omega : V.Vector3) →
  Strain.fourierStrainMultiplier
      (Scale.scaledProjectionMode scale modeData) omega
  ≡ Strain.fourierStrainMultiplier modeData omega
scaledStrainMultiplierUnchanged = Scale.fourierStrainMultiplierScaleInvariant

record KineticStrainScaleContrast
    (scale : Threshold.PositiveThreshold)
    (modeData : V.ProjectionMode)
    (omega : V.Vector3)
    (transverse : V.dot (V.mode modeData) omega ≡ 0ℚ) : Set where
  field
    velocityNormGainsInverseSquare :
      V.normSquared
          (BS.biotSavart (Scale.scaledProjectionMode scale modeData) omega)
      ≡
      (Threshold.thresholdInverse scale * Threshold.thresholdInverse scale)
        * V.normSquared (BS.biotSavart modeData omega)

    strainMultiplierHasNoScaleGain :
      Strain.fourierStrainMultiplier
          (Scale.scaledProjectionMode scale modeData) omega
      ≡ Strain.fourierStrainMultiplier modeData omega

open KineticStrainScaleContrast public

kineticStrainScaleContrast :
  (scale : Threshold.PositiveThreshold) →
  (modeData : V.ProjectionMode) →
  (omega : V.Vector3) →
  (transverse : V.dot (V.mode modeData) omega ≡ 0ℚ) →
  KineticStrainScaleContrast scale modeData omega transverse
kineticStrainScaleContrast scale modeData omega transverse = record
  { velocityNormGainsInverseSquare =
      scaledBiotSavartNormSquared scale modeData omega transverse
  ; strainMultiplierHasNoScaleGain =
      scaledStrainMultiplierUnchanged scale modeData omega
  }

hhGoodOrderZeroStrainKineticCompensationNoGoClosed : Bool
hhGoodOrderZeroStrainKineticCompensationNoGoClosed = true

hhGoodKineticRepairMustRecoverInverseDerivativeBeforeOrderZeroKernel : Bool
hhGoodKineticRepairMustRecoverInverseDerivativeBeforeOrderZeroKernel = true

hhGoodOrderZeroStrainKineticCompensationNoGoClosedIsTrue :
  hhGoodOrderZeroStrainKineticCompensationNoGoClosed ≡ true
hhGoodOrderZeroStrainKineticCompensationNoGoClosedIsTrue = refl
