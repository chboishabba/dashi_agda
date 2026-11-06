{-# OPTIONS --safe #-}
module DASHI.Foundations.BishopRound11FiniteParityDegreeZeroExact where

------------------------------------------------------------------------
-- K05 ORIGINAL FACTORIAL BINOMIAL DEGREE ZERO: BOTH COORDINATES.
--
-- This module discharges the base case of the two missing source
-- coefficient identities, on the ACTUAL Round11 cosine/sine signed
-- factorial functions. It is independent of a general trigonometric
-- product law, and uses only the original Fin-Cauchy degree-zero
-- lemma and the original Bishop real polynomial ring solver.
--
-- The positive-degree induction / all-n binomial coefficient
-- transport remains a different open proof. Nothing in this module
-- identifies a finite regression with an unbounded proof.
--
-- Sources: Bishop/Bridges; Murray and Csimma pinned Bishop carrier;
-- original DASHI Round11 factorial and finite Fin-sum authors.
-- Source-written, Agda 2.9 kernel acceptance pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (zero)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)

import Real as R
import RealProperties as RP

import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Terms
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Analysis.BishopRound11NativeComplexRectangleExact as Round11
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Cutset
import DASHI.Foundations.BishopGroupedCauchyParityTelescopeExact as Telescope

cosineFirstOriginalFactorial :
  (x : R.ℝ) →
  R._≃_ (Terms.cosineSignedTerm x zero) R.1ℝ
cosineFirstOriginalFactorial x =
  let open RP.ℝ-Solver
  in solve 0
    ((Κ 1ℚᵘ ⊗ (Κ 1ℚᵘ ⊗ Κ 1ℚᵘ)) ⊜ Κ 1ℚᵘ)
    RP.≃-refl

sineFirstOriginalFactorial :
  (x : R.ℝ) →
  R._≃_ (Terms.sineSignedTerm x zero) x
sineFirstOriginalFactorial x =
  let open RP.ℝ-Solver
  in solve 1
    (λ value →
      (Κ 1ℚᵘ ⊗ (Κ 1ℚᵘ ⊗ (Κ 1ℚᵘ ⊗ value)))
      ⊜ value)
    RP.≃-refl x

cosineCosineFirstCoefficient :
  (x y : R.ℝ) →
  R._≃_
    (Row.cauchyCoefficient
      (Terms.cosineSignedTerm x)
      (Terms.cosineSignedTerm y)
      zero)
    R.1ℝ
cosineCosineFirstCoefficient x y =
  RP.≃-trans
    (Row.cauchyCoefficientZero
      (Terms.cosineSignedTerm x)
      (Terms.cosineSignedTerm y))
    (RP.≃-trans
      (RP.*-cong
        (cosineFirstOriginalFactorial x)
        (cosineFirstOriginalFactorial y))
      (RP.*-identityˡ R.1ℝ))

cosineSineFirstCoefficient :
  (x y : R.ℝ) →
  R._≃_
    (Row.cauchyCoefficient
      (Terms.cosineSignedTerm x)
      (Terms.sineSignedTerm y)
      zero)
    y
cosineSineFirstCoefficient x y =
  RP.≃-trans
    (Row.cauchyCoefficientZero
      (Terms.cosineSignedTerm x)
      (Terms.sineSignedTerm y))
    (RP.≃-trans
      (RP.*-cong
        (cosineFirstOriginalFactorial x)
        (sineFirstOriginalFactorial y))
      (RP.*-identityˡ y))

sineCosineFirstCoefficient :
  (x y : R.ℝ) →
  R._≃_
    (Row.cauchyCoefficient
      (Terms.sineSignedTerm x)
      (Terms.cosineSignedTerm y)
      zero)
    x
sineCosineFirstCoefficient x y =
  RP.≃-trans
    (Row.cauchyCoefficientZero
      (Terms.sineSignedTerm x)
      (Terms.cosineSignedTerm y))
    (RP.≃-trans
      (RP.*-cong
        (sineFirstOriginalFactorial x)
        (cosineFirstOriginalFactorial y))
      (RP.*-identityʳ x))

originalEvenFactorialBinomialDegreeZero :
  (inputs : Cutset.Round11BishopCutset) →
  (x y : R.ℝ) →
  R._≃_
    (R._-_
      (Round11.round11CosCosDegree inputs x y zero)
      (Telescope.previousCoefficient
        (Round11.round11SinSinDegree inputs x y) zero))
    (Round11.round11OriginalCosineSourceDegree inputs x y zero)
originalEvenFactorialBinomialDegreeZero inputs x y =
  RP.≃-trans
    (RP.+-congʳ
      (R.-_ R.0ℝ)
      (cosineCosineFirstCoefficient x y))
    (RP.≃-trans
      (let open RP.ℝ-Solver
       in solve 0
          ((Κ 1ℚᵘ ⊖ Κ 0ℚᵘ) ⊜ Κ 1ℚᵘ)
          RP.≃-refl)
      (RP.≃-symm (cosineFirstOriginalFactorial (R._+_ x y))))

originalOddFactorialBinomialDegreeZero :
  (inputs : Cutset.Round11BishopCutset) →
  (x y : R.ℝ) →
  R._≃_
    (R._+_
      (Round11.round11CosSinDegree inputs x y zero)
      (Round11.round11SinCosDegree inputs x y zero))
    (Round11.round11OriginalSineSourceDegree inputs x y zero)
originalOddFactorialBinomialDegreeZero inputs x y =
  RP.≃-trans
    (RP.+-cong
      (cosineSineFirstCoefficient x y)
      (sineCosineFirstCoefficient x y))
    (RP.≃-trans
      (RP.+-comm y x)
      (RP.≃-symm (sineFirstOriginalFactorial (R._+_ x y))))
