module DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres; Agda standard-library
-- contributors; DASHI repository contributors.
-- Title: "A Multilinear Schur Test and Multiplier Operators" and
-- "Canonical positive shell-kernel majorant for output relocation".
-- Venue/year: Journal of Functional Analysis 187 (2001), 1--24; Agda
-- standard library; DASHI formal development, 2026.
-- DOI: 10.1006/jfan.2001.3804; the repository majorant has no DOI.
-- Uses: positivity and finite-sum monotonicity for the canonical factorised
-- shell kernel M(j,d) = (1/4)^j (1/32)^d, together with the exact rational
-- geometric bounds 4/3, 32/31 and 128/93.
-- Relationship: constructs a genuinely nonnegative cutoff-independent shell
-- majorant and proves its exact finite-rectangle bound.  Identifying the
-- absolute Navier--Stokes output-relocation coefficient with a term dominated
-- by this majorant remains the separate H^s power-comparison bridge.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq
  using (cong; subst; sym)
open Eq.≡-Reasoning

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo

sumTo : (Nat → ℚ) → Nat → ℚ
sumTo values zero = values zero
sumTo values (suc cutoff) = values (suc cutoff) + sumTo values cutoff

sumToMonotone : ∀ left right cutoff →
  (∀ index → left index ≤ right index) →
  sumTo left cutoff ≤ sumTo right cutoff
sumToMonotone left right zero pointwise = pointwise zero
sumToMonotone left right (suc cutoff) pointwise =
  ℚₚ.+-mono-≤
    (pointwise (suc cutoff))
    (sumToMonotone left right cutoff pointwise)

sumToNonnegative : ∀ values cutoff →
  (∀ index → 0ℚ ≤ values index) →
  0ℚ ≤ sumTo values cutoff
sumToNonnegative values zero pointwise = pointwise zero
sumToNonnegative values (suc cutoff) pointwise =
  ℚₚ.+-mono-≤
    (pointwise (suc cutoff))
    (sumToNonnegative values cutoff pointwise)

scaleSumAux : ∀ scale p s →
  scale * p + scale * s ≡ scale * (p + s)
scaleSumAux scale p s = solve (scale ∷ p ∷ s ∷ [])

scaleSum : ∀ scale values cutoff →
  sumTo (λ index → scale * values index) cutoff
  ≡ scale * sumTo values cutoff
scaleSum scale values zero = refl
scaleSum scale values (suc cutoff) =
  begin
    sumTo (λ index → scale * values index) (suc cutoff)
  ≡⟨ cong
       (λ rest → scale * values (suc cutoff) + rest)
       (scaleSum scale values cutoff) ⟩
    scale * values (suc cutoff) + scale * sumTo values cutoff
  ≡⟨ scaleSumAux scale (values (suc cutoff)) (sumTo values cutoff) ⟩
    scale * (values (suc cutoff) + sumTo values cutoff)
  ≡⟨ refl ⟩
    scale * sumTo values (suc cutoff)
  ∎

rightScaleSumAux : ∀ p s scale →
  p * scale + s * scale ≡ (p + s) * scale
rightScaleSumAux p s scale = solve (p ∷ s ∷ scale ∷ [])

rightScaleSum : ∀ values scale cutoff →
  sumTo (λ index → values index * scale) cutoff
  ≡ sumTo values cutoff * scale
rightScaleSum values scale zero = refl
rightScaleSum values scale (suc cutoff) =
  begin
    sumTo (λ index → values index * scale) (suc cutoff)
  ≡⟨ cong
       (λ rest → values (suc cutoff) * scale + rest)
       (rightScaleSum values scale cutoff) ⟩
    values (suc cutoff) * scale + sumTo values cutoff * scale
  ≡⟨ rightScaleSumAux (values (suc cutoff)) (sumTo values cutoff) scale ⟩
    (values (suc cutoff) + sumTo values cutoff) * scale
  ≡⟨ refl ⟩
    sumTo values (suc cutoff) * scale
  ∎

powerSumMeaning : ∀ ratio cutoff →
  sumTo (Geo.pow ratio) cutoff ≡ Geo.partialSum ratio cutoff
powerSumMeaning ratio zero = refl
powerSumMeaning ratio (suc cutoff) =
  cong
    (λ rest → Geo.pow ratio (suc cutoff) + rest)
    (powerSumMeaning ratio cutoff)

rowSum : (Nat → Nat → ℚ) → Nat → Nat → ℚ
rowSum kernel lowShell gapCutoff =
  sumTo (kernel lowShell) gapCutoff

rectangleSum : (Nat → Nat → ℚ) → Nat → Nat → ℚ
rectangleSum kernel lowCutoff gapCutoff =
  sumTo (λ lowShell → rowSum kernel lowShell gapCutoff) lowCutoff

record PositiveFactorizedKernel : Set where
  constructor factorized-kernel
  field
    kernel : Nat → Nat → ℚ
    lowFactor gapFactor : Nat → ℚ

    kernelNonnegative : ∀ lowShell gap → 0ℚ ≤ kernel lowShell gap
    lowFactorNonnegative : ∀ lowShell → 0ℚ ≤ lowFactor lowShell
    gapFactorNonnegative : ∀ gap → 0ℚ ≤ gapFactor gap

    kernelDominatedByFactors : ∀ lowShell gap →
      kernel lowShell gap ≤ lowFactor lowShell * gapFactor gap
    lowFactorDominatedByQuarter : ∀ lowShell →
      lowFactor lowShell ≤ Geo.pow Geo.quarter lowShell
    gapFactorDominatedByThirtySecond : ∀ gap →
      gapFactor gap ≤ Geo.pow Geo.thirtySecond gap

open PositiveFactorizedKernel public

lowFactorSumBound : ∀ K lowCutoff →
  sumTo (lowFactor K) lowCutoff ≤ Geo.fourThirds
lowFactorSumBound K lowCutoff =
  let
    toPowerSum :
      sumTo (lowFactor K) lowCutoff
      ≤ sumTo (Geo.pow Geo.quarter) lowCutoff
    toPowerSum =
      sumToMonotone
        (lowFactor K)
        (Geo.pow Geo.quarter)
        lowCutoff
        (lowFactorDominatedByQuarter K)

    powerSumBound :
      sumTo (Geo.pow Geo.quarter) lowCutoff ≤ Geo.fourThirds
    powerSumBound =
      subst
        (λ sum → sum ≤ Geo.fourThirds)
        (sym (powerSumMeaning Geo.quarter lowCutoff))
        (Geo.quarterPartialSumBound lowCutoff)
  in
  ℚₚ.≤-trans toPowerSum powerSumBound

gapFactorSumBound : ∀ K gapCutoff →
  sumTo (gapFactor K) gapCutoff ≤ Geo.thirtyTwoThirtyFirsts
gapFactorSumBound K gapCutoff =
  let
    toPowerSum :
      sumTo (gapFactor K) gapCutoff
      ≤ sumTo (Geo.pow Geo.thirtySecond) gapCutoff
    toPowerSum =
      sumToMonotone
        (gapFactor K)
        (Geo.pow Geo.thirtySecond)
        gapCutoff
        (gapFactorDominatedByThirtySecond K)

    powerSumBound :
      sumTo (Geo.pow Geo.thirtySecond) gapCutoff
      ≤ Geo.thirtyTwoThirtyFirsts
    powerSumBound =
      subst
        (λ sum → sum ≤ Geo.thirtyTwoThirtyFirsts)
        (sym (powerSumMeaning Geo.thirtySecond gapCutoff))
        (Geo.thirtySecondPartialSumBound gapCutoff)
  in
  ℚₚ.≤-trans toPowerSum powerSumBound

kernelRowBound : ∀ K lowShell gapCutoff →
  rowSum (kernel K) lowShell gapCutoff
  ≤ lowFactor K lowShell * sumTo (gapFactor K) gapCutoff
kernelRowBound K lowShell gapCutoff =
  let
    termwise :
      rowSum (kernel K) lowShell gapCutoff
      ≤ sumTo
          (λ gap → lowFactor K lowShell * gapFactor K gap)
          gapCutoff
    termwise =
      sumToMonotone
        (kernel K lowShell)
        (λ gap → lowFactor K lowShell * gapFactor K gap)
        gapCutoff
        (kernelDominatedByFactors K lowShell)
  in
  subst
    (λ upper → rowSum (kernel K) lowShell gapCutoff ≤ upper)
    (scaleSum (lowFactor K lowShell) (gapFactor K) gapCutoff)
    termwise

kernelRectangleFactorBound : ∀ K lowCutoff gapCutoff →
  rectangleSum (kernel K) lowCutoff gapCutoff
  ≤ sumTo (lowFactor K) lowCutoff * sumTo (gapFactor K) gapCutoff
kernelRectangleFactorBound K lowCutoff gapCutoff =
  let
    gapTotal = sumTo (gapFactor K) gapCutoff

    rowwise :
      rectangleSum (kernel K) lowCutoff gapCutoff
      ≤ sumTo (λ lowShell → lowFactor K lowShell * gapTotal) lowCutoff
    rowwise =
      sumToMonotone
        (λ lowShell → rowSum (kernel K) lowShell gapCutoff)
        (λ lowShell → lowFactor K lowShell * gapTotal)
        lowCutoff
        (λ lowShell → kernelRowBound K lowShell gapCutoff)
  in
  subst
    (λ upper → rectangleSum (kernel K) lowCutoff gapCutoff ≤ upper)
    (rightScaleSum (lowFactor K) gapTotal lowCutoff)
    rowwise

factorProductBound : ∀ K lowCutoff gapCutoff →
  sumTo (lowFactor K) lowCutoff * sumTo (gapFactor K) gapCutoff
  ≤ Geo.oneTwentyEightNinetyThirds
factorProductBound K lowCutoff gapCutoff =
  let
    gapSumNonnegative =
      sumToNonnegative
        (gapFactor K) gapCutoff (gapFactorNonnegative K)

    firstStep :
      sumTo (lowFactor K) lowCutoff * sumTo (gapFactor K) gapCutoff
      ≤ Geo.fourThirds * sumTo (gapFactor K) gapCutoff
    firstStep =
      let
        instance
          gapSumIsNonnegative = nonNegative gapSumNonnegative
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (sumTo (gapFactor K) gapCutoff)
        (lowFactorSumBound K lowCutoff)

    secondStep :
      Geo.fourThirds * sumTo (gapFactor K) gapCutoff
      ≤ Geo.fourThirds * Geo.thirtyTwoThirtyFirsts
    secondStep =
      let
        instance
          fourThirdsIsNonnegative =
            nonNegative Geo.fourThirdsNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        Geo.fourThirds
        (gapFactorSumBound K gapCutoff)

    productBound :
      sumTo (lowFactor K) lowCutoff * sumTo (gapFactor K) gapCutoff
      ≤ Geo.fourThirds * Geo.thirtyTwoThirtyFirsts
    productBound = ℚₚ.≤-trans firstStep secondStep
  in
  subst
    (λ upper →
      sumTo (lowFactor K) lowCutoff * sumTo (gapFactor K) gapCutoff
      ≤ upper)
    Geo.productConstantIdentity
    productBound

kernelRectangleBound : ∀ K lowCutoff gapCutoff →
  rectangleSum (kernel K) lowCutoff gapCutoff
  ≤ Geo.oneTwentyEightNinetyThirds
kernelRectangleBound K lowCutoff gapCutoff =
  ℚₚ.≤-trans
    (kernelRectangleFactorBound K lowCutoff gapCutoff)
    (factorProductBound K lowCutoff gapCutoff)

canonicalKernel : Nat → Nat → ℚ
canonicalKernel lowShell gap =
  Geo.pow Geo.quarter lowShell * Geo.pow Geo.thirtySecond gap

canonicalKernelNonnegative : ∀ lowShell gap →
  0ℚ ≤ canonicalKernel lowShell gap
canonicalKernelNonnegative lowShell gap =
  let
    lowNonnegative =
      Geo.powNonnegative
        Geo.quarter lowShell Geo.quarterNonnegative
    gapNonnegative =
      Geo.powNonnegative
        Geo.thirtySecond gap Geo.thirtySecondNonnegative
    instance
      lowIsNonnegative = nonNegative lowNonnegative
      gapIsNonnegative = nonNegative gapNonnegative
      productIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (Geo.pow Geo.quarter lowShell)
          (Geo.pow Geo.thirtySecond gap)
  in
  ℚₚ.nonNegative⁻¹
    (Geo.pow Geo.quarter lowShell * Geo.pow Geo.thirtySecond gap)

canonicalPositiveFactorizedKernel : PositiveFactorizedKernel
canonicalPositiveFactorizedKernel = factorized-kernel
  canonicalKernel
  (Geo.pow Geo.quarter)
  (Geo.pow Geo.thirtySecond)
  canonicalKernelNonnegative
  (λ lowShell →
    Geo.powNonnegative Geo.quarter lowShell Geo.quarterNonnegative)
  (λ gap →
    Geo.powNonnegative Geo.thirtySecond gap Geo.thirtySecondNonnegative)
  (λ lowShell gap → ℚₚ.≤-refl)
  (λ lowShell → ℚₚ.≤-refl)
  (λ gap → ℚₚ.≤-refl)

canonicalKernelCutoffUniformBound : ∀ lowCutoff gapCutoff →
  rectangleSum canonicalKernel lowCutoff gapCutoff
  ≤ Geo.oneTwentyEightNinetyThirds
canonicalKernelCutoffUniformBound =
  kernelRectangleBound canonicalPositiveFactorizedKernel

outputRelocationPositiveKernelConstructed : Bool
outputRelocationPositiveKernelConstructed = true

outputRelocationPositiveKernelNonnegative : Bool
outputRelocationPositiveKernelNonnegative = true

outputRelocationPositiveKernelCutoffUniformlySummable : Bool
outputRelocationPositiveKernelCutoffUniformlySummable = true

outputRelocationPositiveKernelConstructedIsTrue :
  outputRelocationPositiveKernelConstructed ≡ true
outputRelocationPositiveKernelConstructedIsTrue = refl

outputRelocationPositiveKernelNonnegativeIsTrue :
  outputRelocationPositiveKernelNonnegative ≡ true
outputRelocationPositiveKernelNonnegativeIsTrue = refl

outputRelocationPositiveKernelCutoffUniformlySummableIsTrue :
  outputRelocationPositiveKernelCutoffUniformlySummable ≡ true
outputRelocationPositiveKernelCutoffUniformlySummableIsTrue = refl
