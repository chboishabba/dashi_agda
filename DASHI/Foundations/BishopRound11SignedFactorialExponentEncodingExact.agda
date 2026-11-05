{-# OPTIONS --safe #-}
module DASHI.Foundations.BishopRound11SignedFactorialExponentEncodingExact where

------------------------------------------------------------------------
-- K05 SIGNED SOURCE FACTORIAL ↔ EXISTING EXPONENTIAL COEFFICIENT.
--
-- The Round11 signed cosine/sine terms are not synthetic phases.
-- Their literal denominators are exactly the factorial denominators
-- already used in BishopExponentialFiniteCauchyCoefficientExact.
--
-- Every n:
--   cosTerm(x,n) ~= (-1)^n expTerm(x,2n)
--   sinTerm(x,n) ~= (-1)^n expTerm(x,2n+1).
-- The proof uses the original Bishop setoid-real carrier and simple
-- multiplication commutativity, and identifies BOTH recursive
-- exponent families with the original doubled-index function.
--
-- No complex exponential or sine-addition law is assumed here.
-- Original owners: Newton/binomial, Cauchy; Bishop/Bridges;
-- Murray/Csimma pinned backend; DASHI Round11 factorial terms.
-- Kernel acceptance pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)

import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopConvergentDoubleTailExact as Double
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimates
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Terms

evenExponentIsDoubledIndex :
  (n : Nat) →
  Estimates.evenExponent n ≡ Double.double n
evenExponentIsDoubledIndex zero = refl
evenExponentIsDoubledIndex (suc n) =
  cong suc (cong suc (evenExponentIsDoubledIndex n))

oddExponentIsSuccessorDoubled :
  (n : Nat) →
  Estimates.oddExponent n ≡ suc (Double.double n)
oddExponentIsSuccessorDoubled zero = refl
oddExponentIsSuccessorDoubled (suc n) =
  cong suc (cong suc (oddExponentIsSuccessorDoubled n))

cosineTermIsSignedExponentialEvenCoefficient :
  (x : R.ℝ) →
  (n : Nat) →
  R._≃_
    (Terms.cosineSignedTerm x n)
    (R._*_
      (Terms.alternatingSign n)
      (Exp.expTerm x (Double.double n)))
cosineTermIsSignedExponentialEvenCoefficient x n =
  RP.≃-trans
    (RP.*-congˡ
      (RP.*-comm
        (R._⋆ (Estimates.inverseFactorialRational
          (Estimates.evenExponent n)))
        (R.pow x (Estimates.evenExponent n))))
    (RP.*-congˡ
      (RP.≃-refl₂
        (cong (Exp.expTerm x)
          (evenExponentIsDoubledIndex n))))

sineTermIsSignedExponentialOddCoefficient :
  (x : R.ℝ) →
  (n : Nat) →
  R._≃_
    (Terms.sineSignedTerm x n)
    (R._*_
      (Terms.alternatingSign n)
      (Exp.expTerm x (suc (Double.double n))))
sineTermIsSignedExponentialOddCoefficient x n =
  RP.≃-trans
    (RP.*-congˡ
      (RP.*-comm
        (R._⋆ (Estimates.inverseFactorialRational
          (Estimates.oddExponent n)))
        (R.pow x (Estimates.oddExponent n))))
    (RP.*-congˡ
      (RP.≃-refl₂
        (cong (Exp.expTerm x)
          (oddExponentIsSuccessorDoubled n))))

alternatingSignAddition :
  (left right : Nat) →
  R._≃_
    (R._*_
      (Terms.alternatingSign left)
      (Terms.alternatingSign right))
    (Terms.alternatingSign (left + right))
alternatingSignAddition left right =
  RP.xⁿxᵐ≃xⁿ⁺ᵐ
    Terms.bishopMinusOne left right


------------------------------------------------------------------------
-- SOURCE-NATIVE SIGNS AT EVERY EVEN/ODD FACTORIAL DEGREE.
-- The base (-1)^2=1 uses Round11's original negated-square proof;
-- the inductive step uses the pinned all-N power-addition theorem.
------------------------------------------------------------------------

alternatingSignTwoIsOne :
  R._≃_
    (Terms.alternatingSign (suc (suc zero)))
    R.1ℝ
alternatingSignTwoIsOne =
  RP.≃-trans
    (RP.*-congʳ
      (RP.*-identityˡ Terms.bishopMinusOne))
    (RP.≃-trans
      (Terms.negatedSquareEquivalentSquare R.1ℝ)
      (RP.*-identityˡ R.1ℝ))

alternatingSignEvenIndexIsOne :
  (n : Nat) →
  R._≃_
    (Terms.alternatingSign (Double.double n))
    R.1ℝ
alternatingSignEvenIndexIsOne zero = RP.≃-refl
alternatingSignEvenIndexIsOne (suc n) =
  RP.≃-trans
    (RP.≃-symm
      (alternatingSignAddition
        (suc (suc zero)) (Double.double n)))
    (RP.≃-trans
      (RP.*-cong
        alternatingSignTwoIsOne
        (alternatingSignEvenIndexIsOne n))
      (RP.*-identityˡ R.1ℝ))

alternatingSignOddIndexIsMinusOne :
  (n : Nat) →
  R._≃_
    (Terms.alternatingSign (suc (Double.double n)))
    Terms.bishopMinusOne
alternatingSignOddIndexIsMinusOne n =
  RP.≃-trans
    (RP.*-congʳ (alternatingSignEvenIndexIsOne n))
    (RP.*-identityˡ Terms.bishopMinusOne)
