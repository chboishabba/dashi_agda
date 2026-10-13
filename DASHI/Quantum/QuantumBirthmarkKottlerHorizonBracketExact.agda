{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkKottlerHorizonBracketExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.List.Base using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; _/_; _+_; _-_; _*_; _<_)
open import Data.Rational.Properties as ℚP using (_<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Foundations.GRQFTDeSitterKottlerJunctionExact as Junction

------------------------------------------------------------------------
-- HORIZON POLYNOMIAL FOR THE SELECTED KOTTLER EXTERIOR
--
-- M=1/4, Lambda_out=3/16 gives
--   f(r)=1 - 1/(2r) - r^2/16.
-- For r>0, f(r)=0 iff
--   p(r)=r^3-16r+8=0.
-- Local Python locates positive roots near 0.508203 and 3.721612.  Here we
-- store exact rational sign brackets around them.  The shell R=2 lies between
-- those brackets and already has f(R)=1/2>0 in the repo fixture.
------------------------------------------------------------------------

horizonPolynomial : ℚ → ℚ
horizonPolynomial radius =
  radius * radius * radius
  - (Int.+ 16 / 1) * radius
  + (Int.+ 8 / 1)

innerLeft : ℚ
innerLeft = Int.+ 1 / 2

innerRight : ℚ
innerRight = Int.+ 13 / 25

outerLeft : ℚ
outerLeft = Int.+ 37 / 10

outerRight : ℚ
outerRight = Int.+ 15 / 4

innerLeftValue :
  horizonPolynomial innerLeft ≡ Int.+ 1 / 8
innerLeftValue = solve []

innerRightValue :
  horizonPolynomial innerRight ≡ - (Int.+ 2803 / 15625)
innerRightValue = solve []

outerLeftValue :
  horizonPolynomial outerLeft ≡ - (Int.+ 547 / 1000)
outerLeftValue = solve []

outerRightValue :
  horizonPolynomial outerRight ≡ Int.+ 47 / 64
outerRightValue = solve []

innerHorizonBracket :
  0ℚ < horizonPolynomial innerLeft
  × horizonPolynomial innerRight < 0ℚ
innerHorizonBracket =
  toWitness {a? = 0ℚ ℚP.<? horizonPolynomial innerLeft} _ ,
  toWitness {a? = horizonPolynomial innerRight ℚP.<? 0ℚ} _

outerHorizonBracket :
  horizonPolynomial outerLeft < 0ℚ
  × 0ℚ < horizonPolynomial outerRight
outerHorizonBracket =
  toWitness {a? = horizonPolynomial outerLeft ℚP.<? 0ℚ} _ ,
  toWitness {a? = 0ℚ ℚP.<? horizonPolynomial outerRight} _

shellRadiusInsideStaticPatch :
  Junction.fExterior
    Junction.fixtureRadius Junction.fixtureMass Junction.lambdaOut
  ≡ Int.+ 1 / 2
shellRadiusInsideStaticPatch = Junction.fixtureExteriorLapseIsOneHalf

positiveHorizonSignBracketsOwned : Bool
positiveHorizonSignBracketsOwned = true

shellBetweenPositiveHorizonBrackets : Bool
shellBetweenPositiveHorizonBrackets = true

rootExistenceFromContinuityAuthorityStillRequired : Bool
rootExistenceFromContinuityAuthorityStillRequired = true

maximalHorizonExtensionStillRequired : Bool
maximalHorizonExtensionStillRequired = true

globalGeodesicCompletenessStillNotProved : Bool
globalGeodesicCompletenessStillNotProved = true
