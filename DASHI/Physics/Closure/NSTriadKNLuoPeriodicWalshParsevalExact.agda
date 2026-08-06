module DASHI.Physics.Closure.NSTriadKNLuoPeriodicWalshParsevalExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Classical finite Fourier/Parseval theorem on (Z/2Z)^3.
-- Repository-original Agda proof; no DOI is assigned.
--
-- Related reference:
-- Author: Loukas Grafakos.
-- Title: "Classical Fourier Analysis".
-- DOI: 10.1007/978-1-4939-1194-3.
--
-- PURPOSE
-- Instantiate the orthogonality theorem in a complete concrete eight-mode
-- Galerkin transform.  With normalized counting measure and normalized
-- Fourier coefficients,
--
--   (1/8) sum_x f(x)^2 = sum_k fhat(k)^2.
--
-- The proof is a direct checked polynomial identity in the eight physical
-- samples, so no Parseval field or residual is supplied by the caller.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNLuoPeriodicWalshCharacterOrthogonalityExact as Walsh

record Signal8 : Set where
  constructor signal8
  field
    f000 f001 f010 f011 f100 f101 f110 f111 : ℚ

open Signal8 public

oneEighth : ℚ
oneEighth = Int.+ 1 / 8

square : ℚ → ℚ
square value = value * value

rawCoefficient : Signal8 → Walsh.Bit3 → ℚ
rawCoefficient f (Walsh.bit3 Walsh.b0 Walsh.b0 Walsh.b0) =
  f000 f + f001 f + f010 f + f011 f
  + f100 f + f101 f + f110 f + f111 f
rawCoefficient f (Walsh.bit3 Walsh.b0 Walsh.b0 Walsh.b1) =
  f000 f - f001 f + f010 f - f011 f
  + f100 f - f101 f + f110 f - f111 f
rawCoefficient f (Walsh.bit3 Walsh.b0 Walsh.b1 Walsh.b0) =
  f000 f + f001 f - f010 f - f011 f
  + f100 f + f101 f - f110 f - f111 f
rawCoefficient f (Walsh.bit3 Walsh.b0 Walsh.b1 Walsh.b1) =
  f000 f - f001 f - f010 f + f011 f
  + f100 f - f101 f - f110 f + f111 f
rawCoefficient f (Walsh.bit3 Walsh.b1 Walsh.b0 Walsh.b0) =
  f000 f + f001 f + f010 f + f011 f
  - f100 f - f101 f - f110 f - f111 f
rawCoefficient f (Walsh.bit3 Walsh.b1 Walsh.b0 Walsh.b1) =
  f000 f - f001 f + f010 f - f011 f
  - f100 f + f101 f - f110 f + f111 f
rawCoefficient f (Walsh.bit3 Walsh.b1 Walsh.b1 Walsh.b0) =
  f000 f + f001 f - f010 f - f011 f
  - f100 f - f101 f + f110 f + f111 f
rawCoefficient f (Walsh.bit3 Walsh.b1 Walsh.b1 Walsh.b1) =
  f000 f - f001 f - f010 f + f011 f
  - f100 f + f101 f + f110 f - f111 f

normalizedCoefficient : Signal8 → Walsh.Bit3 → ℚ
normalizedCoefficient f mode =
  oneEighth * rawCoefficient f mode

physicalL2Squared : Signal8 → ℚ
physicalL2Squared f =
  oneEighth
  * ( square (f000 f) + square (f001 f)
    + square (f010 f) + square (f011 f)
    + square (f100 f) + square (f101 f)
    + square (f110 f) + square (f111 f))

fourierL2Squared : Signal8 → ℚ
fourierL2Squared f =
    square (normalizedCoefficient f Walsh.p000)
  + square (normalizedCoefficient f Walsh.p001)
  + square (normalizedCoefficient f Walsh.p010)
  + square (normalizedCoefficient f Walsh.p011)
  + square (normalizedCoefficient f Walsh.p100)
  + square (normalizedCoefficient f Walsh.p101)
  + square (normalizedCoefficient f Walsh.p110)
  + square (normalizedCoefficient f Walsh.p111)

rawWalshEnergyIdentity :
  (f : Signal8) →
    square (rawCoefficient f Walsh.p000)
  + square (rawCoefficient f Walsh.p001)
  + square (rawCoefficient f Walsh.p010)
  + square (rawCoefficient f Walsh.p011)
  + square (rawCoefficient f Walsh.p100)
  + square (rawCoefficient f Walsh.p101)
  + square (rawCoefficient f Walsh.p110)
  + square (rawCoefficient f Walsh.p111)
  ≡ Walsh.eight
    * ( square (f000 f) + square (f001 f)
      + square (f010 f) + square (f011 f)
      + square (f100 f) + square (f101 f)
      + square (f110 f) + square (f111 f))
rawWalshEnergyIdentity f =
  solve
    ( f000 f ∷ f001 f ∷ f010 f ∷ f011 f
    ∷ f100 f ∷ f101 f ∷ f110 f ∷ f111 f ∷ [])

periodicWalshParseval :
  (f : Signal8) →
  fourierL2Squared f ≡ physicalL2Squared f
periodicWalshParseval f =
  solve
    ( f000 f ∷ f001 f ∷ f010 f ∷ f011 f
    ∷ f100 f ∷ f101 f ∷ f110 f ∷ f111 f ∷ [])
