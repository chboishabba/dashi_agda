module DASHI.Physics.Closure.NSTriadKNPressureHessianVortexStretchingSplitRound78Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Dhawal Buaria; Alain Pumir.
-- Title: "Role of pressure in generation of intense velocity gradients in
-- turbulent flows".
-- DOI: 10.48550/arXiv.2308.03902.
--
-- ROUND78 / RAW PRESSURE-HESSIAN SIGN DICTIONARY
--
-- Writing W=S omega, the inviscid part of the stretching-production evolution
-- used in Buaria--Pumir is
--
--   D(omega.W)/Dt = W.W - omega^T H omega.
--
-- Split H = H^I + H^D and abbreviate the two vorticity contractions by
--
--   C_I = omega^T H^I omega,
--   C_D = omega^T H^D omega.
--
-- Then exactly
--
--   W2 - (C_I + C_D)
--     = W2 + (-C_D) - C_I.
--
-- Thus a negative deviatoric contraction is an enabling contribution after
-- the PDE minus sign, while a positive isotropic contraction is depleting.
-- This module proves only that exact algebraic split.  The source-native future
-- theorem must construct C_I,C_D from the actual selected pressure Hessian and
-- establish their signs/size on the same event; DNS conditional statistics are
-- not promoted to pointwise proof authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _-_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

record RawPressureStretchingContractions : Set where
  constructor raw-pressure-stretching-contractions
  field
    vortexStretchingSquare : ℚ
    isotropicPressureContraction : ℚ
    deviatoricPressureContraction : ℚ

open RawPressureStretchingContractions public

fullPressureContraction : RawPressureStretchingContractions → ℚ
fullPressureContraction raw =
  isotropicPressureContraction raw + deviatoricPressureContraction raw

inviscidStretchingAcceleration : RawPressureStretchingContractions → ℚ
inviscidStretchingAcceleration raw =
  vortexStretchingSquare raw - fullPressureContraction raw

nonlocalDeviatoricEnable : RawPressureStretchingContractions → ℚ
nonlocalDeviatoricEnable raw = - deviatoricPressureContraction raw

localIsotropicDepletion : RawPressureStretchingContractions → ℚ
localIsotropicDepletion raw = isotropicPressureContraction raw

pressureSplitExact : ∀ raw →
  inviscidStretchingAcceleration raw
  ≡ vortexStretchingSquare raw
      + nonlocalDeviatoricEnable raw
      - localIsotropicDepletion raw
pressureSplitExact raw =
  solve
    ( vortexStretchingSquare raw
    ∷ isotropicPressureContraction raw
    ∷ deviatoricPressureContraction raw
    ∷ [])

round78PressureHessianRawSplitConstructed : Bool
round78PressureHessianRawSplitConstructed = true

round78DNSConditionalSignsPromotedToPointwiseTheorem : Bool
round78DNSConditionalSignsPromotedToPointwiseTheorem = false

round78SelectedTrajectoryPressureContractionsConstructed : Bool
round78SelectedTrajectoryPressureContractionsConstructed = false

round78PressureHessianRawSplitConstructedIsTrue :
  round78PressureHessianRawSplitConstructed ≡ true
round78PressureHessianRawSplitConstructedIsTrue = refl
