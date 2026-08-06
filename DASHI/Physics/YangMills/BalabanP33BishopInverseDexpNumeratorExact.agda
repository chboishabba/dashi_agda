module DASHI.Physics.YangMills.BalabanP33BishopInverseDexpNumeratorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Ethan Eade,
-- "Derivative of the Exponential Map", technical note, 2018 revision.
-- No DOI recorded.
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- The quadratic coefficient of inverse-dexp for the gamma=2 SU(2) convention
-- is controlled by the removable numerator
--
--   n(t) = 2 sin(t) - t (1 + cos(t)).
--
-- This module proves a constructive interval for n(t) from the higher-order
-- Bishop partial sums.  It uses the lower sine / upper cosine pair for the
-- lower endpoint and the upper sine / lower cosine pair for the upper endpoint:
--
--   2 s_7^-(t) - t(1+c_4^+(t))
--       <= n(t)
--       <= 2 s_5^+(t) - t(1+c_6^-(t)).
--
-- The proof is order transport through multiplication by the nonnegative
-- radius.  No cotangent, division, or trigonometric bound is postulated.
------------------------------------------------------------------------

open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.BalabanP33BishopTaylorPolynomialFormExact as Low
import DASHI.Physics.YangMills.BalabanP33BishopHigherOrderTaylorExact as Higher
open import DASHI.Physics.YangMills.CompactLieProofLevel

twice : BishopReal.ℝ → BishopReal.ℝ
twice value = BishopReal._+_ value value

onePlus : BishopReal.ℝ → BishopReal.ℝ
onePlus value = BishopReal._+_ BishopReal.1ℝ value

scaled : BishopReal.ℝ → BishopReal.ℝ → BishopReal.ℝ
scaled radius value = BishopReal._*_ radius value

rawInverseDexpNumerator :
  BishopReal.ℝ → BishopReal.ℝ → BishopReal.ℝ → BishopReal.ℝ
rawInverseDexpNumerator radius sineValue cosineValue =
  BishopReal._+_
    (twice sineValue)
    (BishopReal.- (scaled radius (onePlus cosineValue)))

inverseDexpNumerator :
  Elementary.BishopElementaryPowerSeriesData →
  BishopReal.ℝ → BishopReal.ℝ
inverseDexpNumerator dataSet radius =
  rawInverseDexpNumerator radius
    (Elementary.bishopSin dataSet radius)
    (Elementary.bishopCos dataSet radius)

sineSepticLowerPolynomial sineQuinticUpperPolynomial :
  BishopReal.ℝ → BishopReal.ℝ
sineSepticLowerPolynomial radius =
  BishopReal._+_
    (BishopReal._-_ radius (Low.sineCubicTerm radius))
    (BishopReal._-_
      (Higher.sineQuinticTerm radius)
      (Higher.sineSepticTerm radius))

sineQuinticUpperPolynomial radius =
  BishopReal._+_
    (BishopReal._-_ radius (Low.sineCubicTerm radius))
    (Higher.sineQuinticTerm radius)

cosineQuarticUpperPolynomial cosineSexticLowerPolynomial :
  BishopReal.ℝ → BishopReal.ℝ
cosineQuarticUpperPolynomial radius =
  BishopReal._+_
    (BishopReal._-_ BishopReal.1ℝ
      (Low.cosineQuadraticTerm radius))
    (Higher.cosineQuarticTerm radius)

cosineSexticLowerPolynomial radius =
  BishopReal._+_
    (BishopReal._-_ BishopReal.1ℝ
      (Low.cosineQuadraticTerm radius))
    (BishopReal._-_
      (Higher.cosineQuarticTerm radius)
      (Higher.cosineSexticTerm radius))

inverseDexpNumeratorLowerEnvelope inverseDexpNumeratorUpperEnvelope :
  BishopReal.ℝ → BishopReal.ℝ
inverseDexpNumeratorLowerEnvelope radius =
  rawInverseDexpNumerator radius
    (sineSepticLowerPolynomial radius)
    (cosineQuarticUpperPolynomial radius)

inverseDexpNumeratorUpperEnvelope radius =
  rawInverseDexpNumerator radius
    (sineQuinticUpperPolynomial radius)
    (cosineSexticLowerPolynomial radius)

multiplyLeftMonotoneNonnegative :
  ∀ {left right} radius →
  BishopReal.NonNegative radius →
  BishopReal._≤_ left right →
  BishopReal._≤_
    (BishopReal._*_ radius left)
    (BishopReal._*_ radius right)
multiplyLeftMonotoneNonnegative {left} {right}
    radius radiusNonnegative leftBelowRight =
  BishopProperties.≤-respʳ-≃
    (let open BishopProperties.ℝ-Solver
     in solve 2
        (λ r x → x ⊗ r ⊜ r ⊗ x)
        BishopProperties.≃-refl right radius)
    (BishopProperties.≤-respˡ-≃
      (let open BishopProperties.ℝ-Solver
       in solve 2
          (λ r x → r ⊗ x ⊜ x ⊗ r)
          BishopProperties.≃-refl radius left)
      (BishopProperties.*-monoʳ-≤-nonNeg
        leftBelowRight radiusNonnegative))

rawNumeratorMonotone :
  ∀ radius {sineLower sineValue sineUpper
      cosineLower cosineValue cosineUpper} →
  BishopReal.NonNegative radius →
  BishopReal._≤_ sineLower sineValue →
  BishopReal._≤_ sineValue sineUpper →
  BishopReal._≤_ cosineLower cosineValue →
  BishopReal._≤_ cosineValue cosineUpper →
  BishopReal._≤_
    (rawInverseDexpNumerator radius sineLower cosineUpper)
    (rawInverseDexpNumerator radius sineValue cosineValue)
  ×
  BishopReal._≤_
    (rawInverseDexpNumerator radius sineValue cosineValue)
    (rawInverseDexpNumerator radius sineUpper cosineLower)
rawNumeratorMonotone radius radiusNonnegative
    sineLowerBound sineUpperBound cosineLowerBound cosineUpperBound =
  let
    twiceLower = BishopProperties.+-mono-≤
      sineLowerBound sineLowerBound
    twiceUpper = BishopProperties.+-mono-≤
      sineUpperBound sineUpperBound

    onePlusCosineUpper =
      BishopProperties.+-monoˡ-≤ BishopReal.1ℝ cosineUpperBound
    onePlusCosineLower =
      BishopProperties.+-monoˡ-≤ BishopReal.1ℝ cosineLowerBound

    scaledUpper = multiplyLeftMonotoneNonnegative
      radius radiusNonnegative onePlusCosineUpper
    scaledLower = multiplyLeftMonotoneNonnegative
      radius radiusNonnegative onePlusCosineLower
  in
  BishopProperties.+-mono-≤
    twiceLower
    (BishopProperties.neg-mono-≤ scaledUpper)
  ,
  BishopProperties.+-mono-≤
    twiceUpper
    (BishopProperties.neg-mono-≤ scaledLower)

record InverseDexpNumeratorBounds
    (dataSet : Elementary.BishopElementaryPowerSeriesData)
    (radius : BishopReal.ℝ) : Set₁ where
  field
    lowerEnvelopeBelowNumerator :
      BishopReal._≤_
        (inverseDexpNumeratorLowerEnvelope radius)
        (inverseDexpNumerator dataSet radius)
    numeratorBelowUpperEnvelope :
      BishopReal._≤_
        (inverseDexpNumerator dataSet radius)
        (inverseDexpNumeratorUpperEnvelope radius)

open InverseDexpNumeratorBounds public

inverseDexpNumeratorBounds :
  ∀ {dataSet radius} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet radius →
  InverseDexpNumeratorBounds dataSet radius
inverseDexpNumeratorBounds {dataSet} {radius} inputs =
  let
    bounds = Higher.higherOrderTaylorBounds inputs
    interval = rawNumeratorMonotone radius
      (Concrete.valueNonnegative inputs)
      (Higher.sineSepticLower bounds)
      (Higher.sineQuinticUpper bounds)
      (Higher.cosineSexticLower bounds)
      (Higher.cosineQuarticUpper bounds)
  in
  record
    { lowerEnvelopeBelowNumerator = proj₁ interval
    ; numeratorBelowUpperEnvelope = proj₂ interval
    }

p33BishopInverseDexpNumeratorIntervalLevel : ProofLevel
p33BishopInverseDexpNumeratorIntervalLevel = machineChecked
