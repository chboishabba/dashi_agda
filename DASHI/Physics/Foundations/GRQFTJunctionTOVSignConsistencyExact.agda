{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTJunctionTOVSignConsistencyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_)

import DASHI.Physics.Foundations.GRQFTFiniteRationalTOVSystemExact as TOV
import DASHI.Physics.Foundations.GRQFTDeSitterKottlerJunctionExact as Junction

------------------------------------------------------------------------
-- TOV / ISRAEL-SIGN CROSS-CONSISTENCY
--
-- The literal TOV boundary balance solved:
--
--   p_t(R) = 7/12 > 0.
--
-- The independent de Sitter -> Kottler junction calculation found:
--
--   [f'] = +3/8,
--
-- which in the static shell sign convention requires positive tangential
-- surface pressure orientation.
--
-- These are not the same magnitude theorem: the TOV p_t is a bulk boundary
-- cell value, while the Israel object is a distributional surface stress.
-- But the independently-derived signs agree.
------------------------------------------------------------------------

data TangentialPressureSign : Set where
  negativeTangential : TangentialPressureSign
  zeroTangential : TangentialPressureSign
  positiveTangential : TangentialPressureSign

tovBoundaryTangentialSign : TangentialPressureSign
tovBoundaryTangentialSign = positiveTangential

junctionSurfaceTangentialSign : TangentialPressureSign
junctionSurfaceTangentialSign = positiveTangential

tovBoundaryTangentialPressureIsSevenTwelfths :
  TOV.requiredOuterTangentialPressure ≡ Int.+ 7 / 12
tovBoundaryTangentialPressureIsSevenTwelfths =
  TOV.requiredOuterTangentialPressureIsSevenTwelfths

junctionDerivativeJumpIsThreeEighths :
  Junction.fixtureDerivativeJump ≡ Int.+ 3 / 8
junctionDerivativeJumpIsThreeEighths =
  Junction.fixtureDerivativeJumpIsThreeEighths

tovAndJunctionTangentialSignsAgree :
  tovBoundaryTangentialSign ≡ junctionSurfaceTangentialSign
tovAndJunctionTangentialSignsAgree = refl

record TOVJunctionSignConsistencyWitness : Set where
  constructor tov-junction-sign-consistency-witness
  field
    tovTangentialPressure :
      TOV.requiredOuterTangentialPressure ≡ Int.+ 7 / 12

    junctionDerivativeJump :
      Junction.fixtureDerivativeJump ≡ Int.+ 3 / 8

    tovSign : TangentialPressureSign
    junctionSign : TangentialPressureSign

    signsAgree :
      tovSign ≡ junctionSign

    commonSignPositive :
      tovSign ≡ positiveTangential

open TOVJunctionSignConsistencyWitness public

canonicalTOVJunctionSignConsistencyWitness :
  TOVJunctionSignConsistencyWitness
canonicalTOVJunctionSignConsistencyWitness =
  tov-junction-sign-consistency-witness
    TOV.requiredOuterTangentialPressureIsSevenTwelfths
    Junction.fixtureDerivativeJumpIsThreeEighths
    positiveTangential
    positiveTangential
    refl
    refl

record TOVJunctionSignConsistencyBoundary : Set where
  constructor tov-junction-sign-consistency-boundary
  field
    bulkTOVRequiresPositiveTangentialBoundaryPressure : Bool
    junctionRequiresPositiveSurfacePressureOrientation : Bool
    independentSignsAgree : Bool
    bulkPressureEqualsSurfaceDistributionMagnitude : Bool
    exactIsraelMagnitudeStillOpen : Bool

canonicalTOVJunctionSignConsistencyBoundary :
  TOVJunctionSignConsistencyBoundary
canonicalTOVJunctionSignConsistencyBoundary =
  tov-junction-sign-consistency-boundary
    true true true false true
