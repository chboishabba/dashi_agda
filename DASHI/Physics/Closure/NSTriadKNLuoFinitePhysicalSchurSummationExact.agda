module DASHI.Physics.Closure.NSTriadKNLuoFinitePhysicalSchurSummationExact where

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
-- Prove the finite physical Schur summation step itself.  A pointwise
-- interaction bound
--
--   A(j,d) <= (1/4)^j (1/32)^d G E
--
-- is summed over every finite shell rectangle and gives the shell-independent
-- estimate
--
--   sum_{j<=J,d<=D} A(j,d) <= (128/93) G E.
--
-- No whole-sum estimate is accepted as an input.  The proof consists of
-- nested finite-sum monotonicity, exact factor extraction, and the repository's
-- already-proved geometric kernel bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality as Eq
  using (cong₂; subst)
open Eq.≡-Reasoning

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Majorant

rectangleSumMonotone :
  ∀ left right lowCutoff gapCutoff →
  (∀ lowShell gap → left lowShell gap ≤ right lowShell gap) →
  Majorant.rectangleSum left lowCutoff gapCutoff
  ≤ Majorant.rectangleSum right lowCutoff gapCutoff
rectangleSumMonotone left right lowCutoff gapCutoff pointwise =
  Majorant.sumToMonotone
    (λ lowShell → Majorant.rowSum left lowShell gapCutoff)
    (λ lowShell → Majorant.rowSum right lowShell gapCutoff)
    lowCutoff
    (λ lowShell →
      Majorant.sumToMonotone
        (left lowShell)
        (right lowShell)
        gapCutoff
        (pointwise lowShell))

rectangleRightScale :
  ∀ kernel scale lowCutoff gapCutoff →
  Majorant.rectangleSum
    (λ lowShell gap → kernel lowShell gap * scale)
    lowCutoff gapCutoff
  ≡ Majorant.rectangleSum kernel lowCutoff gapCutoff * scale
rectangleRightScale kernel scale zero gapCutoff =
  Majorant.rightScaleSum (kernel zero) scale gapCutoff
rectangleRightScale kernel scale (suc lowCutoff) gapCutoff =
  begin
    Majorant.rectangleSum
      (λ lowShell gap → kernel lowShell gap * scale)
      (suc lowCutoff) gapCutoff
  ≡⟨ refl ⟩
    Majorant.rowSum
      (λ lowShell gap → kernel lowShell gap * scale)
      (suc lowCutoff) gapCutoff
    + Majorant.rectangleSum
        (λ lowShell gap → kernel lowShell gap * scale)
        lowCutoff gapCutoff
  ≡⟨ cong₂ _+_
       (Majorant.rightScaleSum
         (kernel (suc lowCutoff)) scale gapCutoff)
       (rectangleRightScale kernel scale lowCutoff gapCutoff) ⟩
    Majorant.rowSum kernel (suc lowCutoff) gapCutoff * scale
    + Majorant.rectangleSum kernel lowCutoff gapCutoff * scale
  ≡⟨ Majorant.rightScaleSumAux
       (Majorant.rowSum kernel (suc lowCutoff) gapCutoff)
       (Majorant.rectangleSum kernel lowCutoff gapCutoff)
       scale ⟩
    (Majorant.rowSum kernel (suc lowCutoff) gapCutoff
      + Majorant.rectangleSum kernel lowCutoff gapCutoff) * scale
  ≡⟨ refl ⟩
    Majorant.rectangleSum kernel (suc lowCutoff) gapCutoff * scale
  ∎

record FinitePhysicalSchurData : Set where
  constructor finite-physical-schur
  field
    pairMagnitude : Nat → Nat → ℚ
    lowGradient weightedEnergy : ℚ

    lowGradientNonnegative : 0ℚ ≤ lowGradient
    weightedEnergyNonnegative : 0ℚ ≤ weightedEnergy
    pairMagnitudeNonnegative :
      ∀ lowShell gap → 0ℚ ≤ pairMagnitude lowShell gap

    pointwisePhysicalSchur :
      ∀ lowShell gap →
      pairMagnitude lowShell gap
      ≤ Majorant.canonicalKernel lowShell gap
          * (lowGradient * weightedEnergy)

open FinitePhysicalSchurData public

schurCommonFactor : FinitePhysicalSchurData → ℚ
schurCommonFactor data =
  lowGradient data * weightedEnergy data

schurCommonFactorNonnegative :
  (data : FinitePhysicalSchurData) →
  0ℚ ≤ schurCommonFactor data
schurCommonFactorNonnegative data =
  let
    instance
      gradientIsNonnegative =
        nonNegative (lowGradientNonnegative data)
      energyIsNonnegative =
        nonNegative (weightedEnergyNonnegative data)
      productIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (lowGradient data)
          (weightedEnergy data)
  in
  ℚₚ.nonNegative⁻¹
    (lowGradient data * weightedEnergy data)

finitePhysicalSchurRectangleBound :
  (data : FinitePhysicalSchurData) →
  (lowCutoff gapCutoff : Nat) →
  Majorant.rectangleSum
    (pairMagnitude data) lowCutoff gapCutoff
  ≤ Geo.oneTwentyEightNinetyThirds * schurCommonFactor data
finitePhysicalSchurRectangleBound data lowCutoff gapCutoff =
  let
    common = schurCommonFactor data

    toScaledKernel :
      Majorant.rectangleSum
        (pairMagnitude data) lowCutoff gapCutoff
      ≤ Majorant.rectangleSum
          (λ lowShell gap →
            Majorant.canonicalKernel lowShell gap * common)
          lowCutoff gapCutoff
    toScaledKernel =
      rectangleSumMonotone
        (pairMagnitude data)
        (λ lowShell gap →
          Majorant.canonicalKernel lowShell gap * common)
        lowCutoff gapCutoff
        (pointwisePhysicalSchur data)

    toKernelTimesCommon :
      Majorant.rectangleSum
        (pairMagnitude data) lowCutoff gapCutoff
      ≤ Majorant.rectangleSum
          Majorant.canonicalKernel lowCutoff gapCutoff
          * common
    toKernelTimesCommon =
      subst
        (λ upper →
          Majorant.rectangleSum
            (pairMagnitude data) lowCutoff gapCutoff
          ≤ upper)
        (rectangleRightScale
          Majorant.canonicalKernel common lowCutoff gapCutoff)
        toScaledKernel

    kernelTimesCommonBound :
      Majorant.rectangleSum
        Majorant.canonicalKernel lowCutoff gapCutoff
        * common
      ≤ Geo.oneTwentyEightNinetyThirds * common
    kernelTimesCommonBound =
      let
        instance
          commonIsNonnegative =
            nonNegative (schurCommonFactorNonnegative data)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        common
        (Majorant.canonicalKernelCutoffUniformBound
          lowCutoff gapCutoff)
  in
  ℚₚ.≤-trans toKernelTimesCommon kernelTimesCommonBound

finitePhysicalSchurPointwiseToRectangleClosed : Bool
finitePhysicalSchurPointwiseToRectangleClosed = true

finitePhysicalSchurConstantIsExact : Bool
finitePhysicalSchurConstantIsExact = true

finitePhysicalSchurPointwiseToRectangleClosedIsTrue :
  finitePhysicalSchurPointwiseToRectangleClosed ≡ true
finitePhysicalSchurPointwiseToRectangleClosedIsTrue = refl

finitePhysicalSchurConstantIsExactIsTrue :
  finitePhysicalSchurConstantIsExact ≡ true
finitePhysicalSchurConstantIsExactIsTrue = refl
