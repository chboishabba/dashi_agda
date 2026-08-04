module DASHI.Physics.Closure.NSTriadKNLuoFiniteFourInteractionSchurBoundsExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Loukas Grafakos; Rodolfo H. Torres.
-- Title: "A Multilinear Schur Test and Multiplier Operators".
-- Journal of Functional Analysis 187 (2001), 1--24.
-- DOI: 10.1006/jfan.2001.3804.
--
-- PURPOSE
-- Apply the exact finite physical Schur summation theorem to the four
-- interaction families occurring in the Section-4 decomposition:
--
--   J11 lower, J11 upper, J12, and J2.
--
-- Each family is assumed only pointwise dominated by the canonical positive
-- shell kernel times one common low-gradient/weighted-energy factor.  The
-- four finite rectangle estimates and their exact aggregate constant 512/93
-- are then proved, rather than accepted as whole-sum leaves.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Integer.Base as Int
open import Data.List.Base using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _/_; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Majorant
import DASHI.Physics.Closure.NSTriadKNLuoFinitePhysicalSchurSummationExact as Schur

record FiniteFourInteractionData : Set where
  constructor finite-four-interaction
  field
    j11LowerMagnitude : Nat → Nat → ℚ
    j11UpperMagnitude : Nat → Nat → ℚ
    j12Magnitude : Nat → Nat → ℚ
    j2Magnitude : Nat → Nat → ℚ

    lowGradient weightedEnergy : ℚ
    lowGradientNonnegative : 0ℚ ≤ lowGradient
    weightedEnergyNonnegative : 0ℚ ≤ weightedEnergy

    j11LowerNonnegative :
      ∀ lowShell gap → 0ℚ ≤ j11LowerMagnitude lowShell gap
    j11UpperNonnegative :
      ∀ lowShell gap → 0ℚ ≤ j11UpperMagnitude lowShell gap
    j12Nonnegative :
      ∀ lowShell gap → 0ℚ ≤ j12Magnitude lowShell gap
    j2Nonnegative :
      ∀ lowShell gap → 0ℚ ≤ j2Magnitude lowShell gap

    j11LowerPointwise :
      ∀ lowShell gap →
      j11LowerMagnitude lowShell gap
      ≤ Majorant.canonicalKernel lowShell gap
          * (lowGradient * weightedEnergy)

    j11UpperPointwise :
      ∀ lowShell gap →
      j11UpperMagnitude lowShell gap
      ≤ Majorant.canonicalKernel lowShell gap
          * (lowGradient * weightedEnergy)

    j12Pointwise :
      ∀ lowShell gap →
      j12Magnitude lowShell gap
      ≤ Majorant.canonicalKernel lowShell gap
          * (lowGradient * weightedEnergy)

    j2Pointwise :
      ∀ lowShell gap →
      j2Magnitude lowShell gap
      ≤ Majorant.canonicalKernel lowShell gap
          * (lowGradient * weightedEnergy)

open FiniteFourInteractionData public

j11LowerSchurData :
  FiniteFourInteractionData → Schur.FinitePhysicalSchurData
j11LowerSchurData data =
  Schur.finite-physical-schur
    (j11LowerMagnitude data)
    (lowGradient data)
    (weightedEnergy data)
    (lowGradientNonnegative data)
    (weightedEnergyNonnegative data)
    (j11LowerNonnegative data)
    (j11LowerPointwise data)

j11UpperSchurData :
  FiniteFourInteractionData → Schur.FinitePhysicalSchurData
j11UpperSchurData data =
  Schur.finite-physical-schur
    (j11UpperMagnitude data)
    (lowGradient data)
    (weightedEnergy data)
    (lowGradientNonnegative data)
    (weightedEnergyNonnegative data)
    (j11UpperNonnegative data)
    (j11UpperPointwise data)

j12SchurData :
  FiniteFourInteractionData → Schur.FinitePhysicalSchurData
j12SchurData data =
  Schur.finite-physical-schur
    (j12Magnitude data)
    (lowGradient data)
    (weightedEnergy data)
    (lowGradientNonnegative data)
    (weightedEnergyNonnegative data)
    (j12Nonnegative data)
    (j12Pointwise data)

j2SchurData :
  FiniteFourInteractionData → Schur.FinitePhysicalSchurData
j2SchurData data =
  Schur.finite-physical-schur
    (j2Magnitude data)
    (lowGradient data)
    (weightedEnergy data)
    (lowGradientNonnegative data)
    (weightedEnergyNonnegative data)
    (j2Nonnegative data)
    (j2Pointwise data)

section4CommonFactor : FiniteFourInteractionData → ℚ
section4CommonFactor data =
  lowGradient data * weightedEnergy data

j11LowerFiniteBound :
  (data : FiniteFourInteractionData) →
  (lowCutoff gapCutoff : Nat) →
  Majorant.rectangleSum
    (j11LowerMagnitude data) lowCutoff gapCutoff
  ≤ Geo.oneTwentyEightNinetyThirds * section4CommonFactor data
j11LowerFiniteBound data =
  Schur.finitePhysicalSchurRectangleBound
    (j11LowerSchurData data)

j11UpperFiniteBound :
  (data : FiniteFourInteractionData) →
  (lowCutoff gapCutoff : Nat) →
  Majorant.rectangleSum
    (j11UpperMagnitude data) lowCutoff gapCutoff
  ≤ Geo.oneTwentyEightNinetyThirds * section4CommonFactor data
j11UpperFiniteBound data =
  Schur.finitePhysicalSchurRectangleBound
    (j11UpperSchurData data)

j12FiniteBound :
  (data : FiniteFourInteractionData) →
  (lowCutoff gapCutoff : Nat) →
  Majorant.rectangleSum
    (j12Magnitude data) lowCutoff gapCutoff
  ≤ Geo.oneTwentyEightNinetyThirds * section4CommonFactor data
j12FiniteBound data =
  Schur.finitePhysicalSchurRectangleBound
    (j12SchurData data)

j2FiniteBound :
  (data : FiniteFourInteractionData) →
  (lowCutoff gapCutoff : Nat) →
  Majorant.rectangleSum
    (j2Magnitude data) lowCutoff gapCutoff
  ≤ Geo.oneTwentyEightNinetyThirds * section4CommonFactor data
j2FiniteBound data =
  Schur.finitePhysicalSchurRectangleBound
    (j2SchurData data)

section4TotalMagnitude :
  FiniteFourInteractionData → Nat → Nat → ℚ
section4TotalMagnitude data lowCutoff gapCutoff =
  ((Majorant.rectangleSum
      (j11LowerMagnitude data) lowCutoff gapCutoff
    + Majorant.rectangleSum
        (j11UpperMagnitude data) lowCutoff gapCutoff)
    + Majorant.rectangleSum
        (j12Magnitude data) lowCutoff gapCutoff)
  + Majorant.rectangleSum
      (j2Magnitude data) lowCutoff gapCutoff

section4AggregateConstant : ℚ
section4AggregateConstant = Int.+ 512 / 93

section4AggregateConstantMeaning :
  ((Geo.oneTwentyEightNinetyThirds
      + Geo.oneTwentyEightNinetyThirds)
    + Geo.oneTwentyEightNinetyThirds)
  + Geo.oneTwentyEightNinetyThirds
  ≡ section4AggregateConstant
section4AggregateConstantMeaning = solve []

fourCommonBoundsAggregate :
  ∀ common →
  (((Geo.oneTwentyEightNinetyThirds * common
      + Geo.oneTwentyEightNinetyThirds * common)
    + Geo.oneTwentyEightNinetyThirds * common)
    + Geo.oneTwentyEightNinetyThirds * common)
  ≡ section4AggregateConstant * common
fourCommonBoundsAggregate common = solve (common ∷ [])

section4TotalFiniteBound :
  (data : FiniteFourInteractionData) →
  (lowCutoff gapCutoff : Nat) →
  section4TotalMagnitude data lowCutoff gapCutoff
  ≤ section4AggregateConstant * section4CommonFactor data
section4TotalFiniteBound data lowCutoff gapCutoff =
  let
    common = section4CommonFactor data
    each = Geo.oneTwentyEightNinetyThirds * common

    fourBounds :
      section4TotalMagnitude data lowCutoff gapCutoff
      ≤ (((each + each) + each) + each)
    fourBounds =
      ℚₚ.+-mono-≤
        (ℚₚ.+-mono-≤
          (ℚₚ.+-mono-≤
            (j11LowerFiniteBound data lowCutoff gapCutoff)
            (j11UpperFiniteBound data lowCutoff gapCutoff))
          (j12FiniteBound data lowCutoff gapCutoff))
        (j2FiniteBound data lowCutoff gapCutoff)
  in
  subst
    (λ upper →
      section4TotalMagnitude data lowCutoff gapCutoff ≤ upper)
    (fourCommonBoundsAggregate common)
    fourBounds

finiteFourSection4SchurBoundsClosed : Bool
finiteFourSection4SchurBoundsClosed = true

finiteSection4AggregateConstantExact : Bool
finiteSection4AggregateConstantExact = true

finiteFourSection4SchurBoundsClosedIsTrue :
  finiteFourSection4SchurBoundsClosed ≡ true
finiteFourSection4SchurBoundsClosedIsTrue = refl

finiteSection4AggregateConstantExactIsTrue :
  finiteSection4AggregateConstantExact ≡ true
finiteSection4AggregateConstantExactIsTrue = refl
