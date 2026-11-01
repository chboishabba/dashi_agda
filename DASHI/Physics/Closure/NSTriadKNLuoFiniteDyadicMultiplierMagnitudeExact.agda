module DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicMultiplierMagnitudeExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Loukas Grafakos; Rodolfo H. Torres.
-- Title: "A Multilinear Schur Test and Multiplier Operators".
-- Journal of Functional Analysis 187 (2001), 1--24.
-- DOI: 10.1006/jfan.2001.3804.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Prove the exact ordered-field step that turns separate low-shell and
-- shell-gap multiplier factors into the canonical Schur kernel
--
--   (1/4)^j (1/32)^d.
--
-- The physical analysis only has to establish the two separate factor bounds;
-- their product, nonnegativity and multiplication by the low gradient are
-- derived here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Majorant

record FiniteDyadicMultiplierProfile : Set where
  constructor finite-dyadic-multiplier
  field
    lowFactor gapFactor : Nat → ℚ
    lowGradient : ℚ

    lowFactorNonnegative :
      (lowShell : Nat) → 0ℚ ≤ lowFactor lowShell
    gapFactorNonnegative :
      (gap : Nat) → 0ℚ ≤ gapFactor gap
    lowGradientNonnegative : 0ℚ ≤ lowGradient

    lowFactorBound :
      (lowShell : Nat) →
      lowFactor lowShell ≤ Geo.pow Geo.quarter lowShell

    gapFactorBound :
      (gap : Nat) →
      gapFactor gap ≤ Geo.pow Geo.thirtySecond gap

open FiniteDyadicMultiplierProfile public

multiplierMagnitude :
  FiniteDyadicMultiplierProfile → Nat → Nat → ℚ
multiplierMagnitude profile lowShell gap =
  lowFactor profile lowShell
  * gapFactor profile gap
  * lowGradient profile

factorProductNonnegative :
  (profile : FiniteDyadicMultiplierProfile) →
  (lowShell gap : Nat) →
  0ℚ ≤ lowFactor profile lowShell * gapFactor profile gap
factorProductNonnegative profile lowShell gap =
  let
    instance
      lowIsNonnegative =
        nonNegative (lowFactorNonnegative profile lowShell)
      gapIsNonnegative =
        nonNegative (gapFactorNonnegative profile gap)
      productIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (lowFactor profile lowShell)
          (gapFactor profile gap)
  in
  ℚₚ.nonNegative⁻¹
    (lowFactor profile lowShell * gapFactor profile gap)

multiplierMagnitudeNonnegative :
  (profile : FiniteDyadicMultiplierProfile) →
  (lowShell gap : Nat) →
  0ℚ ≤ multiplierMagnitude profile lowShell gap
multiplierMagnitudeNonnegative profile lowShell gap =
  let
    instance
      factorsAreNonnegative =
        nonNegative (factorProductNonnegative profile lowShell gap)
      gradientIsNonnegative =
        nonNegative (lowGradientNonnegative profile)
      productIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (lowFactor profile lowShell * gapFactor profile gap)
          (lowGradient profile)
  in
  ℚₚ.nonNegative⁻¹
    (multiplierMagnitude profile lowShell gap)

factorProductBound :
  (profile : FiniteDyadicMultiplierProfile) →
  (lowShell gap : Nat) →
  lowFactor profile lowShell * gapFactor profile gap
  ≤ Majorant.canonicalKernel lowShell gap
factorProductBound profile lowShell gap =
  let
    firstStep :
      lowFactor profile lowShell * gapFactor profile gap
      ≤ Geo.pow Geo.quarter lowShell * gapFactor profile gap
    firstStep =
      let
        instance
          gapIsNonnegative =
            nonNegative (gapFactorNonnegative profile gap)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (gapFactor profile gap)
        (lowFactorBound profile lowShell)

    secondStep :
      Geo.pow Geo.quarter lowShell * gapFactor profile gap
      ≤ Geo.pow Geo.quarter lowShell * Geo.pow Geo.thirtySecond gap
    secondStep =
      let
        instance
          lowPowerIsNonnegative =
            nonNegative
              (Geo.powNonnegative
                Geo.quarter lowShell Geo.quarterNonnegative)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (Geo.pow Geo.quarter lowShell)
        (gapFactorBound profile gap)
  in
  ℚₚ.≤-trans firstStep secondStep

multiplierMagnitudeBound :
  (profile : FiniteDyadicMultiplierProfile) →
  (lowShell gap : Nat) →
  multiplierMagnitude profile lowShell gap
  ≤ Majorant.canonicalKernel lowShell gap
      * lowGradient profile
multiplierMagnitudeBound profile lowShell gap =
  let
    instance
      gradientIsNonnegative =
        nonNegative (lowGradientNonnegative profile)
  in
  ℚₚ.*-monoʳ-≤-nonNeg
    (lowGradient profile)
    (factorProductBound profile lowShell gap)

finiteDyadicFactorProductClosed : Bool
finiteDyadicFactorProductClosed = true

finiteDyadicMultiplierMagnitudeClosed : Bool
finiteDyadicMultiplierMagnitudeClosed = true

finiteDyadicFactorProductClosedIsTrue :
  finiteDyadicFactorProductClosed ≡ true
finiteDyadicFactorProductClosedIsTrue = refl

finiteDyadicMultiplierMagnitudeClosedIsTrue :
  finiteDyadicMultiplierMagnitudeClosed ≡ true
finiteDyadicMultiplierMagnitudeClosedIsTrue = refl
