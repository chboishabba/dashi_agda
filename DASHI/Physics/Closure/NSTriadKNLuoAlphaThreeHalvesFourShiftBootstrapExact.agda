module DASHI.Physics.Closure.NSTriadKNLuoAlphaThreeHalvesFourShiftBootstrapExact where

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
-- PURPOSE
-- Make the fixed high-alpha choice alpha=3/2 and b=4 completely explicit.
-- The corrected predecessor exponent is 7/4, so the four-shell coefficient is
--
--   2^{-4(7/4)} = 2^{-7} = 1/128.
--
-- The four-piece Section-4 Schur constant is 512/93.  Choosing the concrete
-- smallness delta=1/16 gives the absorbed coefficient 32/93.  Hence
--
--   1/128 + 32/93 = 4189/11904 <= 1/2 < 1.
--
-- The module constructs the corresponding absorption and fixed-block
-- recurrence data from primitive boundary/weighted-energy comparisons.  The
-- contraction coefficient is calculated, not assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational using (ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver as Ring using (solve)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNLuoAlphaThreeHalvesConstantsExact as Alpha
import DASHI.Physics.Closure.NSTriadKNLuoFourAlignedAlphaThreeHalvesSummabilityExact as Summability
import DASHI.Physics.Closure.NSTriadKNLuoFiniteFourInteractionSchurBoundsExact as Four
import DASHI.Physics.Closure.NSTriadKNLuoFiniteSmallGradientAbsorptionExact as Absorb
import DASHI.Physics.Closure.NSTriadKNLuoFiniteCutoffSection4RecursionExact as Cutoff
import DASHI.Physics.Closure.NSTriadKNLuoFiniteAbsorbedBlockRecursionExact as Block

one : Nat
one = suc zero

four : Nat
four = suc (suc (suc (suc zero)))

blockShiftIsFourTimesOne : Alpha.fourTimes one ≡ four
blockShiftIsFourTimesOne = refl

boundaryCoefficient smallness absorbedCoefficient : ℚ
boundaryCoefficient = + 1 / 128
smallness = + 1 / 16
absorbedCoefficient = + 32 / 93

combinedCoefficient targetCoefficient : ℚ
combinedCoefficient = boundaryCoefficient + absorbedCoefficient
targetCoefficient = + 1 / 2

correctedCoefficientExact :
  boundaryCoefficient ≡ Alpha.dyadicReciprocalSeventhPower one
correctedCoefficientExact = refl

aggregateSmallnessExact :
  Four.section4AggregateConstant * smallness ≡ absorbedCoefficient
aggregateSmallnessExact = solve []

aggregateSmallnessBelowAbsorption :
  Four.section4AggregateConstant * smallness ≤ absorbedCoefficient
aggregateSmallnessBelowAbsorption
  rewrite aggregateSmallnessExact = ℚₚ.≤-refl

combinedCoefficientExact :
  combinedCoefficient ≡ + 4189 / 11904
combinedCoefficientExact = solve []

combinedCoefficientBelowHalf : combinedCoefficient ≤ targetCoefficient
combinedCoefficientBelowHalf =
  toWitness {a? = combinedCoefficient ≤? targetCoefficient} _

boundaryCoefficientNonnegative : + 0 / 1 ≤ boundaryCoefficient
boundaryCoefficientNonnegative =
  toWitness {a? = (+ 0 / 1) ≤? boundaryCoefficient} _

smallnessNonnegative : + 0 / 1 ≤ smallness
smallnessNonnegative =
  toWitness {a? = (+ 0 / 1) ≤? smallness} _

absorbedCoefficientNonnegative : + 0 / 1 ≤ absorbedCoefficient
absorbedCoefficientNonnegative =
  toWitness {a? = (+ 0 / 1) ≤? absorbedCoefficient} _

targetCoefficientNonnegative : + 0 / 1 ≤ targetCoefficient
targetCoefficientNonnegative =
  toWitness {a? = (+ 0 / 1) ≤? targetCoefficient} _

fixedFourAlignedShift : Alpha.FourAlignedLuoShift
fixedFourAlignedShift = record
  { baseShift = one
  ; blockShift = four
  ; blockShiftMeaning = blockShiftIsFourTimesOne
  ; correctedShiftCoefficient = boundaryCoefficient
  ; correctedCoefficientMeaning = correctedCoefficientExact
  ; AnalyticFractionalPowerMatchesRationalCoefficient =
      boundaryCoefficient ≡ Alpha.dyadicReciprocalSeventhPower one
  ; analyticFractionalPowerMatchesRationalCoefficient =
      correctedCoefficientExact
  }

fixedFourShellRatioIdentification :
  Summability.AnalyticFourShellRatioIdentification
fixedFourShellRatioIdentification = record
  { analyticFourShellRatio = Summability.fourAlignedAlphaThreeHalvesRatio
  ; analyticFourShellRatioMeaning = refl
  ; AnalyticFractionalPowerMeaning =
      Summability.fourAlignedAlphaThreeHalvesRatio
        ≡ Summability.fourAlignedAlphaThreeHalvesRatio
  ; analyticFractionalPowerMeaning = refl
  }

fixedFourAlignedSummability :
  Summability.FourAlignedAlphaThreeHalvesSummability fixedFourAlignedShift
fixedFourAlignedSummability =
  Summability.fourAlignedSummability
    fixedFourAlignedShift
    fixedFourShellRatioIdentification

record ExplicitFourShiftAbsorptionData : Set₁ where
  field
    cutoffData : Cutoff.FiniteCutoffSection4Data
    lowGradientBelowOneSixteenth :
      Four.lowGradient (Cutoff.interactions cutoffData) ≤ smallness

open ExplicitFourShiftAbsorptionData public

explicitAbsorbedCutoff :
  ExplicitFourShiftAbsorptionData → Block.FiniteAbsorbedCutoffData
explicitAbsorbedCutoff data = record
  { cutoffData = cutoffData data
  ; smallness = smallness
  ; absorptionCoefficient = absorbedCoefficient
  ; absorptionCoefficientNonnegative = absorbedCoefficientNonnegative
  ; lowGradientBelowSmallness = lowGradientBelowOneSixteenth data
  ; aggregateSmallnessBelowAbsorption =
      aggregateSmallnessBelowAbsorption
  }

explicitFourPieceAbsorption :
  (data : ExplicitFourShiftAbsorptionData) →
  Cutoff.outputEnergy (cutoffData data)
    + Cutoff.dissipation (cutoffData data)
  ≤ Cutoff.boundaryEnergy (cutoffData data)
      + absorbedCoefficient
          * Four.weightedEnergy
              (Cutoff.interactions (cutoffData data))
explicitFourPieceAbsorption data =
  Block.finiteAbsorbedCutoffInequality (explicitAbsorbedCutoff data)

record ExplicitFourShiftRecursionData : Set₁ where
  field
    absorptionData : ExplicitFourShiftAbsorptionData
    predecessorMajorant : ℚ
    predecessorMajorantNonnegative :
      (+ 0 / 1) ≤ predecessorMajorant

    boundaryEnergyBelowCorrectedPredecessor :
      Cutoff.boundaryEnergy (cutoffData absorptionData)
      ≤ boundaryCoefficient * predecessorMajorant

    weightedEnergyBelowPredecessor :
      Four.weightedEnergy
        (Cutoff.interactions (cutoffData absorptionData))
      ≤ predecessorMajorant

open ExplicitFourShiftRecursionData public

asBlockRecursionData :
  ExplicitFourShiftRecursionData → Block.FiniteBlockRecursionData
asBlockRecursionData data = record
  { absorbedCutoff = explicitAbsorbedCutoff (absorptionData data)
  ; predecessorMajorant = predecessorMajorant data
  ; boundaryCoefficient = boundaryCoefficient
  ; targetCoefficient = targetCoefficient
  ; predecessorMajorantNonnegative =
      predecessorMajorantNonnegative data
  ; boundaryEnergyBelowPredecessor =
      boundaryEnergyBelowCorrectedPredecessor data
  ; weightedEnergyBelowPredecessor =
      weightedEnergyBelowPredecessor data
  ; combinedCoefficientBelowTarget = combinedCoefficientBelowHalf
  }

explicitFourShiftContraction :
  (data : ExplicitFourShiftRecursionData) →
  Cutoff.outputEnergy
      (cutoffData (absorptionData data))
    + Cutoff.dissipation
        (cutoffData (absorptionData data))
  ≤ targetCoefficient * predecessorMajorant data
explicitFourShiftContraction data =
  Block.finiteTargetBlockRecursion (asBlockRecursionData data)
