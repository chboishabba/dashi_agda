module DASHI.Analysis.BishopMachinGeometricBishopRateExact where

------------------------------------------------------------------------
-- K04b2: direct BISHOP-real geometric rate for the actual Machin
-- omitted magnitudes, using the existing stronger x^2 contraction.
--
-- John Machin, 1706; Bishop and Bridges, Constructive Analysis
-- (Springer 1985), DOI 10.1007/978-3-642-61667-9;
-- Zachary Murray, arXiv:2205.08354 (2022); pinned
-- viktorcsimma/bishop RealProperties and the original DASHI
-- BishopMachinArctanConstructionExact.at anMagnitudeSuccessorBelowSquare
-- (name spelled without the space in the actual imported symbol).
--
-- This does not use a new real carrier or a convergence postulate.
-- It proves geometric contraction for both original 1/5 and 1/239
-- terms on the actual Bishop real carrier. The final coefficient
-- 16/5 + 4/239 <= 4 requires its own rational-order bridge.
-- Source-written pending golden Agda kernel check.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
import Data.Nat.Properties as NatP
open import Data.Rational.Unnormalised as Q using (_/_; _≤_; _+_; _*_; *≡*)
import Data.Rational.Unnormalised.Properties as QP
open import Relation.Nullary.Decidable.Core using (toWitness)
import ExtraProperties as Extra
import Real as R
import RealProperties as RP

import DASHI.Foundations.BishopMachinArctanConstructionExact as M
import DASHI.Foundations.BishopMachinPiRationalWindowExact as W
import DASHI.Analysis.BishopMachinRationalStageEmbeddingExact as Rational
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimates
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Square
import DASHI.Analysis.BishopMachinCombinedRemainderBoundExact as Combined

oneOver25 : R.ℝ
oneOver25 = R._⋆ (+ 1 / 25)

one239BelowOne5Rational : M.oneTwoHundredThirtyNinth Q.≤ M.oneFifth
one239BelowOne5Rational =
  Extra.q≤r⇒+p/r≤+p/q 1 5 239 (NatP.m≤m+n 5 234)

one239BelowOne5 :
  R._≤_ M.bishopOneTwoHundredThirtyNinth M.bishopOneFifth
one239BelowOne5 =
  RP.p≤q⇒p⋆≤q⋆
    M.oneTwoHundredThirtyNinth M.oneFifth
    one239BelowOne5Rational

abs239BelowAbs5 :
  R._≤_
    (R.∣_∣ M.bishopOneTwoHundredThirtyNinth)
    (R.∣_∣ M.bishopOneFifth)
abs239BelowAbs5 =
  RP.≤-respʳ-≃
    (RP.≃-symm
      (RP.nonNegx⇒∣x∣≃x M.oneFifthNonnegative))
    (RP.≤-respˡ-≃
      (RP.≃-symm
        (RP.nonNegx⇒∣x∣≃x M.oneTwoHundredThirtyNinthNonnegative))
      one239BelowOne5)

square5EqualsOneOver25 :
  R._≃_
    (Square.bishopMagnitudeSquare M.bishopOneFifth)
    oneOver25
square5EqualsOneOver25 =
  RP.≃-trans
    (RP.*-cong
      (RP.nonNegx⇒∣x∣≃x M.oneFifthNonnegative)
      (RP.nonNegx⇒∣x∣≃x M.oneFifthNonnegative))
    (RP.≃-trans
      (RP.≃-symm (RP.⋆-distrib-* M.oneFifth M.oneFifth))
      (RP.⋆-cong (Q.*≡* refl)))
  where
  open import Agda.Builtin.Equality using (refl)

square239BelowOneOver25 :
  R._≤_
    (Square.bishopMagnitudeSquare M.bishopOneTwoHundredThirtyNinth)
    oneOver25
square239BelowOneOver25 =
  RP.≤-respʳ-≃
    square5EqualsOneOver25
    (RP.*-mono-≤
      (RP.nonNeg∣x∣ M.bishopOneTwoHundredThirtyNinth)
      (RP.nonNeg∣x∣ M.bishopOneTwoHundredThirtyNinth)
      abs239BelowAbs5 abs239BelowAbs5)

oneOver25NonNegative : R.NonNegative oneOver25
oneOver25NonNegative =
  RP.nonNeg-cong square5EqualsOneOver25
    (RP.nonNegx,y⇒nonNegx*y
      (RP.nonNeg∣x∣ M.bishopOneFifth)
      (RP.nonNeg∣x∣ M.bishopOneFifth))

-- Any given native Bishop arctan magnitude with this exact
-- oneOver25 square contract satisfies the same 25-adic decay envelope.
magnitudeStepAtOneOver25 :
  (x : R.ℝ) →
  Square.bishopMagnitudeSquare x R.≤ oneOver25 →
  (n : Nat) →
  M.atanMagnitudeTerm x (suc n)
    R.≤ R._*_ oneOver25 (M.atanMagnitudeTerm x n)
magnitudeStepAtOneOver25 x squareBound n =
  RP.≤-trans
    (M.atanMagnitudeSuccessorBelowSquare x n)
    (RP.*-monoʳ-≤-nonNeg
      squareBound (M.atanMagnitudeNonnegative x n))

geometricMagnitudeBound :
  (x : R.ℝ) →
  Square.bishopMagnitudeSquare x R.≤ oneOver25 →
  (n : Nat) →
  M.atanMagnitudeTerm x n
    R.≤ R._*_
      (R.pow oneOver25 n)
      (M.atanMagnitudeTerm x zero)
geometricMagnitudeBound x squareBound zero =
  RP.≤-reflexive
    (RP.≃-symm (RP.*-identityˡ (M.atanMagnitudeTerm x zero)))
geometricMagnitudeBound x squareBound (suc n) =
  RP.≤-trans
    (magnitudeStepAtOneOver25 x squareBound n)
    (RP.≤-trans
      (RP.*-monoˡ-≤-nonNeg
        (geometricMagnitudeBound x squareBound n)
        oneOver25NonNegative)
      (RP.≤-reflexive
        (let open RP.ℝ-Solver
         in solve 3
           (λ ratio previous initial →
             ratio ⊗ (previous ⊗ initial)
             ⊜ (previous ⊗ ratio) ⊗ initial)
           RP.≃-refl
           oneOver25
           (R.pow oneOver25 n)
           (M.atanMagnitudeTerm x zero))))

fifthGeometricMagnitudeBound : (n : Nat) →
  Combined.magnitude5 n
    R.≤ R._*_
      (R.pow oneOver25 n)
      (Combined.magnitude5 zero)
fifthGeometricMagnitudeBound =
  geometricMagnitudeBound M.bishopOneFifth
    (RP.≤-reflexive square5EqualsOneOver25)

twoHundredThirtyNineGeometricMagnitudeBound : (n : Nat) →
  Combined.magnitude239 n
    R.≤ R._*_
      (R.pow oneOver25 n)
      (Combined.magnitude239 zero)
twoHundredThirtyNineGeometricMagnitudeBound =
  geometricMagnitudeBound M.bishopOneTwoHundredThirtyNinth
    square239BelowOneOver25

-- The output is an original Bishop-real geometric envelope for
-- both source magnitudes; K04b2 finalises by its exact 16/4 base.
weightedMagnitudeBishopGeometric : (n : Nat) →
  R._≤_
    (R._+_
      (R._*_ Combined.sixteen (Combined.magnitude5 n))
      (R._*_ Combined.four (Combined.magnitude239 n)))
    (R._*_
      (R.pow oneOver25 n)
      (R._+_
        (R._*_ Combined.sixteen (Combined.magnitude5 zero))
        (R._*_ Combined.four (Combined.magnitude239 zero))))
weightedMagnitudeBishopGeometric n =
  RP.≤-respʳ-≃
    (let open RP.ℝ-Solver
     in solve 5
       (λ a b ratio c d →
         (a ⊗ (ratio ⊗ c)) ⊕ (b ⊗ (ratio ⊗ d))
         ⊜ ratio ⊗ ((a ⊗ c) ⊕ (b ⊗ d)))
       RP.≃-refl
       Combined.sixteen
       Combined.four
       (R.pow oneOver25 n)
       (Combined.magnitude5 zero)
       (Combined.magnitude239 zero))
    (RP.+-mono-≤
      (RP.*-monoˡ-≤-nonNeg
        (fifthGeometricMagnitudeBound n) W.sixteenNN)
      (RP.*-monoˡ-≤-nonNeg
        (twoHundredThirtyNineGeometricMagnitudeBound n) W.fourNN))

actualMachinBishopGeometricEnvelope : (n : Nat) →
  R._≤_
    (R.∣_∣ (R._-_ M.bishopMachinPi
      (R._⋆ (importedMachinRationalStage n))))
    (R._*_
      (R.pow oneOver25 n)
      (R._+_
        (R._*_ Combined.sixteen (Combined.magnitude5 zero))
        (R._*_ Combined.four (Combined.magnitude239 zero))))
actualMachinBishopGeometricEnvelope n =
  RP.≤-trans
    (Combined.machinRationalAllStagesRemainder n)
    (weightedMagnitudeBishopGeometric n)
  where
  importedMachinRationalStage = Rational.qMachinStage
  open import DASHI.Analysis.BishopMachinRationalStageEmbeddingExact as Rational

------------------------------------------------------------------------
-- Exact base coefficient. No floating-point comparison:
--     16/5 + 4/239 = 3844/1195 <= 4 = 4780/1195.
-- Its rational comparison is decided by the stdlib _≤?_ and lifted to
-- the ACTUAL Bishop source carrier by the original embedding theorem.
------------------------------------------------------------------------

atanMagnitudeZeroIsInput :
  (x : R.ℝ) →
  R.NonNegative x →
  R._≃_ (M.atanMagnitudeTerm x zero) x
atanMagnitudeZeroIsInput x nonnegative =
  RP.≃-trans
    (RP.*-cong
      RP.≃-refl
      (RP.nonNegx⇒∣x∣≃x
        (Concrete.powNonnegative nonnegative
          (Estimates.oddExponent zero))))
    (RP.≃-trans
      (RP.*-identityˡ
        (R.pow x (Estimates.oddExponent zero)))
      (RP.*-identityˡ x))

weightedInitialRational : Q.ℚᵘ
weightedInitialRational =
  (M.sixteen Q.* M.oneFifth)
  Q.+ (M.four Q.* M.oneTwoHundredThirtyNinth)

weightedInitialRationalBelowFour :
  weightedInitialRational Q.≤ M.four
weightedInitialRationalBelowFour =
  toWitness {a? = QP._≤?_ weightedInitialRational M.four} _

weightedInitialBishopEqualsRational :
  R._≃_
    (R._+_
      (R._*_ Combined.sixteen (Combined.magnitude5 zero))
      (R._*_ Combined.four (Combined.magnitude239 zero)))
    (R._⋆ weightedInitialRational)
weightedInitialBishopEqualsRational =
  RP.≃-trans
    (RP.+-cong
      (RP.*-cong RP.≃-refl
        (atanMagnitudeZeroIsInput
          M.bishopOneFifth M.oneFifthNonnegative))
      (RP.*-cong RP.≃-refl
        (atanMagnitudeZeroIsInput
          M.bishopOneTwoHundredThirtyNinth
          M.oneTwoHundredThirtyNinthNonnegative)))
    (RP.≃-trans
      (RP.+-cong
        (RP.≃-symm
          (RP.⋆-distrib-* M.sixteen M.oneFifth))
        (RP.≃-symm
          (RP.⋆-distrib-*
            M.four M.oneTwoHundredThirtyNinth)))
      (RP.≃-symm
        (RP.⋆-distrib-+
          (M.sixteen Q.* M.oneFifth)
          (M.four Q.* M.oneTwoHundredThirtyNinth))))

weightedInitialBishopBelowFour :
  R._≤_
    (R._+_
      (R._*_ Combined.sixteen (Combined.magnitude5 zero))
      (R._*_ Combined.four (Combined.magnitude239 zero)))
    Combined.four
weightedInitialBishopBelowFour =
  RP.≤-respˡ-≃
    (RP.≃-symm weightedInitialBishopEqualsRational)
    (RP.p≤q⇒p⋆≤q⋆
      weightedInitialRational M.four
      weightedInitialRationalBelowFour)

oneOver25PowerNonnegative :
  (n : Nat) → R.NonNegative (R.pow oneOver25 n)
oneOver25PowerNonnegative zero =
  M.embeddedInverseOddNonnegative zero
oneOver25PowerNonnegative (suc n) =
  RP.nonNegx,y⇒nonNegx*y
    (oneOver25PowerNonnegative n)
    oneOver25NonNegative

-- Full K04b: ACTUAL Bishop real error is <= 4*(1/25)^n,
-- on the original same-object pi_M / q_n, for every n (including 0).
machinBishopFourOver25Pow :
  (n : Nat) →
  R._≤_
    (R.∣_∣
      (R._-_ M.bishopMachinPi
        (R._⋆ (Rational.qMachinStage n))))
    (R._*_
      (R.pow oneOver25 n)
      Combined.four)
machinBishopFourOver25Pow n =
  RP.≤-trans
    (actualMachinBishopGeometricEnvelope n)
    (RP.*-monoʳ-≤-nonNeg
      weightedInitialBishopBelowFour
      (oneOver25PowerNonnegative n))

-- Explicit rational 25-adic stage rate; the source theorem is not
-- merely a real-power approximation to an unspecified constant.
machinBishopFourOver25RationalStage :
  (n : Nat) →
  R._≤_
    (R.∣_∣
      (R._-_ M.bishopMachinPi
        (R._⋆ (Rational.qMachinStage n))))
    (R._*_
      (R._⋆ (Rational.qPow (+ 1 / 25) n))
      Combined.four)
machinBishopFourOver25RationalStage n =
  RP.≤-respʳ-≃
    (RP.*-cong
      (RP.≃-symm (Rational.qPowEmbeds (+ 1 / 25) n))
      RP.≃-refl)
    (machinBishopFourOver25Pow n)
