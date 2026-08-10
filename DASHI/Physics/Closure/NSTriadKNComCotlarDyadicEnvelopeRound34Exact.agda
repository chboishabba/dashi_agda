module DASHI.Physics.Closure.NSTriadKNComCotlarDyadicEnvelopeRound34Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Grundlehren der mathematischen Wissenschaften 343, Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- Make the two-sided almost-orthogonality target exact over Q.  Cotlar--Stein
-- summation consumes square roots of pair-product bounds.  To avoid hiding an
-- irrational square-root convention, use the stronger rational target
--
--   ||T_q^* T_r|| , ||T_q T_r^*||
--      <= C^2 * 4^(-|q-r|).
--
-- Its exact square-root envelope is
--
--   C * 2^(-|q-r|),
--
-- because (2^-d)^2 = 4^-d.  The symmetric finite Cotlar mass through shell
-- distance R is proved exactly:
--
--   1 + 2 * sum_{d=1}^R 2^-d
--     = 3 - 2 * 2^-R,
--
-- hence the cutoff-independent limiting mass is 3.
--
-- This does not prove the physical pair-product estimate.  It replaces the
-- vague "some summable decay" target by a concrete rational certificate whose
-- summation constant and tail are exact and cutoff-independent.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 1ℚ; _/_; _+_; _-_; _*_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Dyadic

quarter three : ℚ
quarter = Int.+ 1 / 4
three = Int.+ 3 / 1

quarterDecay : Nat → ℚ
quarterDecay zero = 1ℚ
quarterDecay (suc distance) = quarter * quarterDecay distance

dyadicWeight : Nat → ℚ
dyadicWeight = Dyadic.inverseDyadicScale

dyadicWeightSquareIsQuarterDecay :
  ∀ distance →
  dyadicWeight distance * dyadicWeight distance
  ≡ quarterDecay distance
dyadicWeightSquareIsQuarterDecay zero = refl
dyadicWeightSquareIsQuarterDecay (suc distance)
  rewrite dyadicWeightSquareIsQuarterDecay distance =
  ℚRing.solve-∀ (dyadicWeight distance)

cotlarSymmetricMass : Nat → ℚ
cotlarSymmetricMass zero = 1ℚ
cotlarSymmetricMass (suc radius) =
  cotlarSymmetricMass radius
  + Dyadic.two * dyadicWeight (suc radius)

cotlarSymmetricMassClosedForm :
  ∀ radius →
  cotlarSymmetricMass radius
  ≡ three - Dyadic.two * dyadicWeight radius
cotlarSymmetricMassClosedForm zero = refl
cotlarSymmetricMassClosedForm (suc radius)
  rewrite cotlarSymmetricMassClosedForm radius =
  ℚRing.solve-∀ (dyadicWeight radius)

cotlarSymmetricMassPlusTail :
  ∀ radius →
  cotlarSymmetricMass radius
    + Dyadic.two * dyadicWeight radius
  ≡ three
cotlarSymmetricMassPlusTail radius =
  trans
    (cong
      (λ mass → mass + Dyadic.two * dyadicWeight radius)
      (cotlarSymmetricMassClosedForm radius))
    (ℚRing.solve-∀ (dyadicWeight radius))

rootEnvelope : ℚ → Nat → ℚ
rootEnvelope constant distance =
  constant * dyadicWeight distance

productEnvelope : ℚ → Nat → ℚ
productEnvelope constant distance =
  constant * constant * quarterDecay distance

rootEnvelopeSquaresToProductEnvelope :
  ∀ constant distance →
  rootEnvelope constant distance * rootEnvelope constant distance
  ≡ productEnvelope constant distance
rootEnvelopeSquaresToProductEnvelope constant distance =
  trans
    (ℚRing.solve-∀ constant (dyadicWeight distance))
    (cong
      (constant * constant *_)
      (dyadicWeightSquareIsQuarterDecay distance))

record PhysicalTwoSidedPairProductDatum : Set where
  constructor physical-two-sided-pair-product-datum
  field
    shellDistance : Nat
    constant : ℚ
    leftProductNorm rightProductNorm : ℚ

    leftPairProductUpper :
      leftProductNorm ≤ productEnvelope constant shellDistance
    rightPairProductUpper :
      rightProductNorm ≤ productEnvelope constant shellDistance

open PhysicalTwoSidedPairProductDatum public

pairProductRootBudget :
  PhysicalTwoSidedPairProductDatum → ℚ
pairProductRootBudget datum =
  rootEnvelope (constant datum) (shellDistance datum)

pairProductRootBudgetSquareExact :
  ∀ datum →
  pairProductRootBudget datum * pairProductRootBudget datum
  ≡ productEnvelope (constant datum) (shellDistance datum)
pairProductRootBudgetSquareExact datum =
  rootEnvelopeSquaresToProductEnvelope
    (constant datum) (shellDistance datum)

cotlarRadiusBudget : ℚ → Nat → ℚ
cotlarRadiusBudget constant radius =
  constant * cotlarSymmetricMass radius

cotlarRadiusBudgetPlusTailExact :
  ∀ constant radius →
  cotlarRadiusBudget constant radius
    + constant * Dyadic.two * dyadicWeight radius
  ≡ constant * three
cotlarRadiusBudgetPlusTailExact constant radius =
  trans
    (ℚRing.solve-∀
      constant
      (cotlarSymmetricMass radius)
      (dyadicWeight radius))
    (trans
      (cong
        (constant *_)
        (cotlarSymmetricMassPlusTail radius))
      (ℚRing.solve-∀ constant))

rationalCotlarDyadicEnvelopeClosed : Bool
rationalCotlarDyadicEnvelopeClosed = true

physicalTwoSidedComPairDecayConstructed : Bool
physicalTwoSidedComPairDecayConstructed = false

rationalCotlarDyadicEnvelopeClosedIsTrue :
  rationalCotlarDyadicEnvelopeClosed ≡ true
rationalCotlarDyadicEnvelopeClosedIsTrue = refl

physicalTwoSidedComPairDecayConstructedIsFalse :
  physicalTwoSidedComPairDecayConstructed ≡ false
physicalTwoSidedComPairDecayConstructedIsFalse = refl
