{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopOriginalMachinAtanFiniteDerivativeExact where

------------------------------------------------------------------------
-- K05-PI: DERIVATIVE OF EACH *ORIGINAL* BISHOP MACHIN ATAN TERM.
--
-- Unlike a synthetic polynomial proof, this differentiates the
-- precise selected Atan.atanSignedTerm pointwise:
--   (-1)^n * (1/(2n+1)) * x^(2n+1).
--
-- Its native factor derivative is
--   (-1)^n * x^(2n).
--
-- The proof reuses the ORIGINAL Bishop power derivative, original
-- Nat-scaled embedding, real rational reciprocal cancellation, and
-- original existing alternatingSign. It is division-free as a
-- BishopFactorDerivativeAt, with NO quotient by a nonzero increment.
--
-- Summing via factorDerivativeAdd proves the derivative of every
-- actual finite atan partial, not merely a formal coefficient
-- recurrence. The native uniform derivative-limit interchange and
-- identification with geometricPartial(-x*x) remain separate gates.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)
open import Data.Rational.Unnormalised as Q using (1ℚᵘ; _*_; _≃_; *≡*)

import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Analysis.BishopFactorDerivativeExact as Factor
import DASHI.Analysis.BishopSetoidPowerDerivativeNormalisationExact as Power
import DASHI.Analysis.BishopNaturalScaleEmbeddingBridgeExact as Scale
import DASHI.Foundations.BishopMachinArctanConstructionExact as Atan
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimates
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Terms
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NatReal
import DASHI.Mathematics.NumberTheory.FiniteNatRationalEmbeddingExact as NatEmbed

oddExponentIsSuccessorEven :
  (n : Nat) →
  Estimates.oddExponent n ≡ suc (Estimates.evenExponent n)
oddExponentIsSuccessorEven zero = refl
oddExponentIsSuccessorEven (suc n) =
  cong (λ k → suc (suc k)) (oddExponentIsSuccessorEven n)

oddReciprocalCancelsNat :
  (n : Nat) →
  Q._≃_
    (Q._*_
      (Atan.inverseOddRational n)
      (NatEmbed.natAsRational (Estimates.oddExponent n)))
    Q.1ℚᵘ
oddReciprocalCancelsNat n = Q.*≡* refl

oddReciprocalEmbeddedCancelsNat :
  (n : Nat) →
  R._≃_
    (R._*_
      (R._⋆ (Atan.inverseOddRational n))
      (NatReal.natReal (Estimates.oddExponent n)))
    R.1ℝ
oddReciprocalEmbeddedCancelsNat n =
  RP.≃-trans
    (RP.≃-symm
      (RP.⋆-distrib-*
        (Atan.inverseOddRational n)
        (NatEmbed.natAsRational (Estimates.oddExponent n))))
    (RP.⋆-cong (oddReciprocalCancelsNat n))

sourceOddPowerDerivative :
  (x : R.ℝ) (n : Nat) →
  R._≃_
    (Power.powerDerivative (Estimates.oddExponent n) x)
    (Power.natScale
      (Estimates.oddExponent n)
      (R.pow x (Estimates.evenExponent n)))
sourceOddPowerDerivative x n =
  RP.≃-trans
    (RP.≃-refl₂
      (cong
        (λ k → Power.powerDerivative k x)
        (oddExponentIsSuccessorEven n)))
    (RP.≃-trans
      (Power.powerDerivativeNatScale
        (Estimates.evenExponent n) x)
      (RP.≃-refl₂
        (cong
          (λ k →
            Power.natScale k
              (R.pow x (Estimates.evenExponent n)))
          (symOdd n))))
  where
    symOdd :
      (m : Nat) →
      suc (Estimates.evenExponent m) ≡ Estimates.oddExponent m
    symOdd m = sym (oddExponentIsSuccessorEven m)

sourceOddReciprocalDerivativeCancel :
  (x : R.ℝ) (n : Nat) →
  R._≃_
    (R._*_
      (R._⋆ (Atan.inverseOddRational n))
      (Power.powerDerivative (Estimates.oddExponent n) x))
    (R.pow x (Estimates.evenExponent n))
sourceOddReciprocalDerivativeCancel x n =
  let
    c = R._⋆ (Atan.inverseOddRational n)
    natural = NatReal.natReal (Estimates.oddExponent n)
    p = R.pow x (Estimates.evenExponent n)
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (RP.*-cong
      RP.≃-refl (sourceOddPowerDerivative x n))
    (RP.≃-trans
      (RP.*-cong
        RP.≃-refl
        (Scale.recursiveScaleIsEmbeddedNaturalMultiply
          (Estimates.oddExponent n) p))
      (RP.≃-trans
        (solve 3
          (λ c′ natural′ p′ →
            c′ ⊗ (natural′ ⊗ p′)
            ⊜ (c′ ⊗ natural′) ⊗ p′)
          RP.≃-refl c natural p)
        (RP.≃-trans
          (RP.*-cong
            (oddReciprocalEmbeddedCancelsNat n)
            RP.≃-refl)
          (RP.*-identityˡ p))))

sourceAtanDerivativeTerm : R.ℝ → Nat → R.ℝ
sourceAtanDerivativeTerm x n =
  R._*_
    (Terms.alternatingSign n)
    (R.pow x (Estimates.evenExponent n))

originalMachinAtanTermFactorDerivative :
  (x : R.ℝ) (n : Nat) →
  Factor.BishopFactorDerivativeAt
    (λ y → Atan.atanSignedTerm y n)
    x
    (sourceAtanDerivativeTerm x n)
originalMachinAtanTermFactorDerivative x n =
  Factor.factorDerivativeCongruence
    (λ y → RP.≃-refl)
    (RP.*-cong
      RP.≃-refl
      (sourceOddReciprocalDerivativeCancel x n))
    (Factor.factorDerivativeScale
      (Terms.alternatingSign n)
      (Factor.factorDerivativeScale
        (R._⋆ (Atan.inverseOddRational n))
        (Factor.powerFactorDerivative
          (Estimates.oddExponent n) x)))

sourceAtanFinitePartial : R.ℝ → Nat → R.ℝ
sourceAtanFinitePartial x count =
  Seq.SeriesOf (Atan.atanSignedTerm x) count

sourceAtanDerivativeFinitePartial : R.ℝ → Nat → R.ℝ
sourceAtanDerivativeFinitePartial x count =
  Seq.SeriesOf (sourceAtanDerivativeTerm x) count

originalMachinAtanFinitePartialFactorDerivative :
  (x : R.ℝ) (count : Nat) →
  Factor.BishopFactorDerivativeAt
    (λ y → sourceAtanFinitePartial y count)
    x
    (sourceAtanDerivativeFinitePartial x count)
originalMachinAtanFinitePartialFactorDerivative x zero =
  Factor.factorDerivativeZero x
originalMachinAtanFinitePartialFactorDerivative x (suc count) =
  Factor.factorDerivativeAdd
    (originalMachinAtanFinitePartialFactorDerivative x count)
    (originalMachinAtanTermFactorDerivative x count)
