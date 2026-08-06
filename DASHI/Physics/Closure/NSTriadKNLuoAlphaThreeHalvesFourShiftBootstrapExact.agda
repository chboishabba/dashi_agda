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
-- Instantiate alpha=3/2 and b=4.  The corrected predecessor coefficient is
-- 2^{-4(7/4)}=1/128.  The target four-shell ratio for the weighted criterion
-- quantity is 2^{4(1-alpha)}=1/4.  With the exact four-piece constant 512/93
-- and the concrete smallness delta=1/32, the nonlinear coefficient is 16/93.
-- Therefore
--
--   1/128 + 16/93 = 2141/11904 <= 1/4 < 1.
--
-- Absorption and the fixed-block recurrence are constructed from primitive
-- boundary and weighted-energy comparisons; the contraction coefficient is
-- calculated rather than supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Integer.Base as Int
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNLuoAlphaThreeHalvesConstantsExact as Alpha
import DASHI.Physics.Closure.NSTriadKNLuoFourAlignedAlphaThreeHalvesSummabilityExact as Summability
import DASHI.Physics.Closure.NSTriadKNLuoFiniteFourInteractionSchurBoundsExact as Four
import DASHI.Physics.Closure.NSTriadKNLuoFiniteCutoffSection4RecursionExact as Cutoff
import DASHI.Physics.Closure.NSTriadKNLuoFiniteAbsorbedBlockRecursionExact as Block

one : Nat
one = suc zero

four : Nat
four = suc (suc (suc (suc zero)))

blockShiftIsFourTimesOne : four ≡ Alpha.fourTimes one
blockShiftIsFourTimesOne = refl

boundaryCoefficient smallness absorbedCoefficient : ℚ
boundaryCoefficient = Int.+ 1 / 128
smallness = Int.+ 1 / 32
absorbedCoefficient = Int.+ 16 / 93

combinedCoefficient targetCoefficient : ℚ
combinedCoefficient = boundaryCoefficient + absorbedCoefficient
targetCoefficient = Int.+ 1 / 4

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
  combinedCoefficient ≡ Int.+ 2141 / 11904
combinedCoefficientExact = solve []

combinedCoefficientBelowQuarter : combinedCoefficient ≤ targetCoefficient
combinedCoefficientBelowQuarter =
  toWitness {a? = combinedCoefficient ≤? targetCoefficient} _

boundaryCoefficientNonnegative : 0ℚ ≤ boundaryCoefficient
boundaryCoefficientNonnegative =
  toWitness {a? = 0ℚ ≤? boundaryCoefficient} _

smallnessNonnegative : 0ℚ ≤ smallness
smallnessNonnegative = toWitness {a? = 0ℚ ≤? smallness} _

absorbedCoefficientNonnegative : 0ℚ ≤ absorbedCoefficient
absorbedCoefficientNonnegative =
  toWitness {a? = 0ℚ ≤? absorbedCoefficient} _

targetCoefficientNonnegative : 0ℚ ≤ targetCoefficient
targetCoefficientNonnegative =
  toWitness {a? = 0ℚ ≤? targetCoefficient} _

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
    fixedFourAlignedShift fixedFourShellRatioIdentification

record ExplicitFourShiftAbsorptionData : Set₁ where
  field
    cutoffData : Cutoff.FiniteCutoffSection4Data
    lowGradientBelowOneThirtySecond :
      Four.lowGradient (Cutoff.interactions cutoffData) ≤ smallness

open ExplicitFourShiftAbsorptionData public

explicitAbsorbedCutoff :
  ExplicitFourShiftAbsorptionData → Block.FiniteAbsorbedCutoffData
explicitAbsorbedCutoff data = record
  { cutoffData = cutoffData data
  ; smallness = smallness
  ; absorptionCoefficient = absorbedCoefficient
  ; absorptionCoefficientNonnegative = absorbedCoefficientNonnegative
  ; lowGradientBelowSmallness = lowGradientBelowOneThirtySecond data
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
    predecessorMajorantNonnegative : 0ℚ ≤ predecessorMajorant

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
  ; predecessorMajorantNonnegative = predecessorMajorantNonnegative data
  ; boundaryEnergyBelowPredecessor =
      boundaryEnergyBelowCorrectedPredecessor data
  ; weightedEnergyBelowPredecessor = weightedEnergyBelowPredecessor data
  ; combinedCoefficientBelowTarget = combinedCoefficientBelowQuarter
  }

explicitFourShiftContraction :
  (data : ExplicitFourShiftRecursionData) →
  Cutoff.outputEnergy (cutoffData (absorptionData data))
    + Cutoff.dissipation (cutoffData (absorptionData data))
  ≤ targetCoefficient * predecessorMajorant data
explicitFourShiftContraction data =
  Block.finiteTargetBlockRecursion (asBlockRecursionData data)
