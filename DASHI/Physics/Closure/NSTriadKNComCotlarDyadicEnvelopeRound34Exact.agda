module DASHI.Physics.Closure.NSTriadKNComCotlarDyadicEnvelopeRound34Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Mischa Cotlar; Elias M. Stein.
-- Title: "A unified theory of Hilbert transforms and ergodic theorems".
-- Proceedings of the Symposium on Ergodic Theory, 1955.
-- DOI: not assigned to the cited historical conference article.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- Quantify two exact rational cross-shell targets.
--
-- Direct Round-30 target:
--
--   ||T_q^* T_r|| , ||T_q T_r^*|| <= C 2^(-|q-r|).
--
-- Its symmetric shell-distance mass through radius R is
--
--   C (1 + 2 sum_{d=1}^R 2^-d)
--     = C (3 - 2 * 2^-R),
--
-- with exact limiting mass 3 C.
--
-- Textbook square-root target:
--
--   ||T_q^* T_r|| , ||T_q T_r^*|| <= C^2 4^(-|q-r|).
--
-- The exact rational square-root envelope is C 2^-|q-r| because
-- (2^-d)^2 = 4^-d.  This avoids hiding an irrational square-root convention.
--
-- Neither target is asserted physically here.  The physical theorem remains
-- the two-sided operator estimate for the literal commutator family.  What is
-- now fixed exactly is the decay strength, finite row mass and tail budget that
-- such a theorem must deliver.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 1ℚ; _/_; _+_; _*_; _≤_)
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
cotlarSymmetricMassClosedForm zero = ℚRing.solve []
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

directEnvelope : ℚ → Nat → ℚ
directEnvelope constant distance =
  constant * dyadicWeight distance

directRadiusBudget : ℚ → Nat → ℚ
directRadiusBudget constant radius =
  constant * cotlarSymmetricMass radius

directRadiusBudgetPlusTailExact :
  ∀ constant radius →
  directRadiusBudget constant radius
    + constant * Dyadic.two * dyadicWeight radius
  ≡ constant * three
directRadiusBudgetPlusTailExact constant radius =
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

record PhysicalTwoSidedDirectDyadicDatum : Set where
  constructor physical-two-sided-direct-dyadic-datum
  field
    shellDistance : Nat
    constant : ℚ
    leftProductNorm rightProductNorm : ℚ

    leftDirectUpper :
      leftProductNorm ≤ directEnvelope constant shellDistance
    rightDirectUpper :
      rightProductNorm ≤ directEnvelope constant shellDistance

open PhysicalTwoSidedDirectDyadicDatum public

productEnvelope : ℚ → Nat → ℚ
productEnvelope constant distance =
  constant * constant * quarterDecay distance

rootEnvelope : ℚ → Nat → ℚ
rootEnvelope = directEnvelope

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

record PhysicalTwoSidedSquareRootDatum : Set where
  constructor physical-two-sided-square-root-datum
  field
    squareRootShellDistance : Nat
    squareRootConstant : ℚ
    squareRootLeftProductNorm squareRootRightProductNorm : ℚ

    leftSquareProductUpper :
      squareRootLeftProductNorm
      ≤ productEnvelope squareRootConstant squareRootShellDistance
    rightSquareProductUpper :
      squareRootRightProductNorm
      ≤ productEnvelope squareRootConstant squareRootShellDistance

open PhysicalTwoSidedSquareRootDatum public

squareRootBudget : PhysicalTwoSidedSquareRootDatum → ℚ
squareRootBudget datum =
  rootEnvelope
    (squareRootConstant datum)
    (squareRootShellDistance datum)

squareRootBudgetSquareExact :
  ∀ datum →
  squareRootBudget datum * squareRootBudget datum
  ≡ productEnvelope
      (squareRootConstant datum)
      (squareRootShellDistance datum)
squareRootBudgetSquareExact datum =
  rootEnvelopeSquaresToProductEnvelope
    (squareRootConstant datum)
    (squareRootShellDistance datum)

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
