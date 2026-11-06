{-# OPTIONS --safe #-}
module DASHI.Foundations.BishopUnsignedFactorialCauchyParitySplitExact where

------------------------------------------------------------------------
-- K05: THE ALL-DEGREE FINITE EXPONENTIAL BINOMIAL COEFFICIENT IS
-- SPLIT INTO ITS ACTUAL EVEN/ODD FACTORIAL SOURCES ON BISHOP.ℝ.
--
-- Let A_k = x^k/k!, B_k=y^k/k!, E_k=A_(2k), O_k=A_(2k+1),
-- F_k=B_(2k), G_k=B_(2k+1).
--
-- Every n:
--  C_(2n)(A,B) = C_n(E,F) + C_(n-1)(O,G), n>0;
--  C_0(A,B) = C_0(E,F);
--  C_(2n+1)(A,B) = C_n(E,G) + C_n(O,F).
--
-- The Finset reindex is obtained from the source-native finite
-- even/odd Cauchy split, Fin-to-Series bridge, and stdlib exact
-- Nat ∸ parity identities. The terminal equalities use the ORIGINAL
-- all-degree Bishop exponential Cauchy theorem, not a new axiom.
-- This is *unsigned* algebra. Signs are a separate precise source
-- translation onto the real Round11 sine/cosine histories.
--
-- Mathematical sources: Newton, binomial theorem, Cauchy.
-- Constructive owners: Bishop/Bridges, Murray/Csimma pinned,
-- DASHI original Fin-sum and factorial Cauchy coefficient machinery.
-- --safe source written; Agda-2.9 kernel acceptance outstanding.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (toℕ)
import Data.Fin.Properties as FinP
import Data.Nat.Base as N
open import Relation.Binary.PropositionalEquality using (cong)

import Algebra.Properties.Semiring.Sum as SemiringSum
import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopConvergentDoubleTailExact as Double
import DASHI.Foundations.BishopFiniteEvenOddCauchyReindexExact as Parity
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopFinSumSeriesBridgeExact as FinSum
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialFiniteCauchyCoefficientExact as Coeff

module BishopSum = SemiringSum RP.+-*-semiring

evenTerms oddTerms : (Nat → R.ℝ) → Nat → R.ℝ
evenTerms terms n = terms (Double.double n)
oddTerms terms n = terms (suc (Double.double n))

evenCauchyParityPart :
  (left right : Nat → R.ℝ) →
  (n : Nat) →
  R._≃_
    (Parity.evenPartial
      (Parity.cauchySummand left right (Double.double n))
      (suc n))
    (Row.cauchyCoefficient
      (evenTerms left) (evenTerms right) n)
evenCauchyParityPart left right n =
  RP.≃-trans
    (RP.≃-symm
      (FinSum.finSumIsSeriesOf
        (λ k →
          Parity.cauchySummand left right
            (Double.double n) (Double.double k))
        (suc n)))
    (BishopSum.sum-cong-≋
      (λ index →
        RP.*-congˡ
          (RP.≃-refl₂
            (cong right
              (Parity.doubleDifference n (toℕ index))))))

oddCauchyParityPartEvenSuc :
  (left right : Nat → R.ℝ) →
  (m : Nat) →
  R._≃_
    (Parity.oddPartial
      (Parity.cauchySummand left right
        (Double.double (suc m)))
      (suc m))
    (Row.cauchyCoefficient
      (oddTerms left) (oddTerms right) m)
oddCauchyParityPartEvenSuc left right m =
  RP.≃-trans
    (RP.≃-symm
      (FinSum.finSumIsSeriesOf
        (λ k →
          Parity.cauchySummand left right
            (Double.double (suc m))
            (suc (Double.double k)))
        (suc m)))
    (BishopSum.sum-cong-≋
      (λ index →
        RP.*-congˡ
          (RP.≃-refl₂
            (cong right
              (Parity.evenOddComplement
                (suc m) (toℕ index)
                (FinP.toℕ<n index))))))

evenCauchyCoefficientZero :
  (left right : Nat → R.ℝ) →
  R._≃_
    (Row.cauchyCoefficient left right (Double.double zero))
    (Row.cauchyCoefficient
      (evenTerms left) (evenTerms right) zero)
evenCauchyCoefficientZero left right =
  RP.≃-trans
    (Parity.finiteCauchyEvenDegreeSplit left right zero)
    (RP.≃-trans
      (RP.+-cong
        (evenCauchyParityPart left right zero)
        RP.≃-refl)
      (RP.+-identityʳ
        (Row.cauchyCoefficient
          (evenTerms left) (evenTerms right) zero)))

evenCauchyCoefficientSuccessor :
  (left right : Nat → R.ℝ) →
  (m : Nat) →
  R._≃_
    (Row.cauchyCoefficient left right
      (Double.double (suc m)))
    (R._+_
      (Row.cauchyCoefficient
        (evenTerms left) (evenTerms right) (suc m))
      (Row.cauchyCoefficient
        (oddTerms left) (oddTerms right) m))
evenCauchyCoefficientSuccessor left right m =
  RP.≃-trans
    (Parity.finiteCauchyEvenDegreeSplit left right (suc m))
    (RP.+-cong
      (evenCauchyParityPart left right (suc m))
      (oddCauchyParityPartEvenSuc left right m))

evenCauchyParityPartOdd :
  (left right : Nat → R.ℝ) →
  (n : Nat) →
  R._≃_
    (Parity.evenPartial
      (Parity.cauchySummand left right
        (suc (Double.double n)))
      (suc n))
    (Row.cauchyCoefficient
      (evenTerms left) (oddTerms right) n)
evenCauchyParityPartOdd left right n =
  RP.≃-trans
    (RP.≃-symm
      (FinSum.finSumIsSeriesOf
        (λ k →
          Parity.cauchySummand left right
            (suc (Double.double n))
            (Double.double k))
        (suc n)))
    (BishopSum.sum-cong-≋
      (λ index →
        RP.*-congˡ
          (RP.≃-refl₂
            (cong right
              (Parity.oddEvenComplement
                n (toℕ index)
                (FinP.toℕ≤pred[n] index))))))

oddCauchyParityPartOdd :
  (left right : Nat → R.ℝ) →
  (n : Nat) →
  R._≃_
    (Parity.oddPartial
      (Parity.cauchySummand left right
        (suc (Double.double n)))
      (suc n))
    (Row.cauchyCoefficient
      (oddTerms left) (evenTerms right) n)
oddCauchyParityPartOdd left right n =
  RP.≃-trans
    (RP.≃-symm
      (FinSum.finSumIsSeriesOf
        (λ k →
          Parity.cauchySummand left right
            (suc (Double.double n))
            (suc (Double.double k)))
        (suc n)))
    (BishopSum.sum-cong-≋
      (λ index →
        RP.*-congˡ
          (RP.≃-refl₂
            (cong right
              (Parity.oddOddComplement n (toℕ index))))))

oddCauchyCoefficient :
  (left right : Nat → R.ℝ) →
  (n : Nat) →
  R._≃_
    (Row.cauchyCoefficient left right
      (suc (Double.double n)))
    (R._+_
      (Row.cauchyCoefficient
        (evenTerms left) (oddTerms right) n)
      (Row.cauchyCoefficient
        (oddTerms left) (evenTerms right) n))
oddCauchyCoefficient left right n =
  RP.≃-trans
    (Parity.finiteCauchyOddDegreeSplit left right n)
    (RP.+-cong
      (evenCauchyParityPartOdd left right n)
      (oddCauchyParityPartOdd left right n))

evenExp oddExp : R.ℝ → Nat → R.ℝ
evenExp x n = Exp.expTerm x (Double.double n)
oddExp x n = Exp.expTerm x (suc (Double.double n))

unsignedEvenExponentialCoefficientZero :
  (x y : R.ℝ) →
  R._≃_
    (Row.cauchyCoefficient
      (evenExp x) (evenExp y) zero)
    (Exp.expTerm (R._+_ x y) (Double.double zero))
unsignedEvenExponentialCoefficientZero x y =
  RP.≃-trans
    (RP.≃-symm
      (evenCauchyCoefficientZero
        (Exp.expTerm x) (Exp.expTerm y)))
    (Coeff.finiteExponentialCauchyCoefficient
      x y (Double.double zero))

unsignedEvenExponentialCoefficientSuccessor :
  (x y : R.ℝ) →
  (m : Nat) →
  R._≃_
    (R._+_
      (Row.cauchyCoefficient
        (evenExp x) (evenExp y) (suc m))
      (Row.cauchyCoefficient
        (oddExp x) (oddExp y) m))
    (Exp.expTerm (R._+_ x y)
      (Double.double (suc m)))
unsignedEvenExponentialCoefficientSuccessor x y m =
  RP.≃-trans
    (RP.≃-symm
      (evenCauchyCoefficientSuccessor
        (Exp.expTerm x) (Exp.expTerm y) m))
    (Coeff.finiteExponentialCauchyCoefficient
      x y (Double.double (suc m)))

unsignedOddExponentialCoefficient :
  (x y : R.ℝ) →
  (n : Nat) →
  R._≃_
    (R._+_
      (Row.cauchyCoefficient
        (evenExp x) (oddExp y) n)
      (Row.cauchyCoefficient
        (oddExp x) (evenExp y) n))
    (Exp.expTerm (R._+_ x y)
      (suc (Double.double n)))
unsignedOddExponentialCoefficient x y n =
  RP.≃-trans
    (RP.≃-symm
      (oddCauchyCoefficient
        (Exp.expTerm x) (Exp.expTerm y) n))
    (Coeff.finiteExponentialCauchyCoefficient
      x y (suc (Double.double n)))
