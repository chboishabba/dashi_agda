module DASHI.Moonshine.AbelBishopFactorialComplexRealAxisTermsExact where

------------------------------------------------------------------------
-- REAL-AXIS COEFFICIENT IDENTITY FOR THE ORIGINAL BISHOP COMPLEX
-- FACTORIAL EXPONENTIAL SOURCE.
--
-- Every finite complex power of (x,0) agrees componentwise with
-- (BishopReal.pow x n,0). Therefore each original finite
-- factorial-complex term at (x,0) is the original vendored
-- BishopExp.expTerm x n in its REAL coordinate, with zero imaginary
-- coordinate.
--
-- This pays an actual finite coefficient/carrier seam. It does NOT
-- yet prove that the full Cartesian expC equals this complex series.
-- No limit, continuity, infinite interchange or "exp authority".
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)

import Real as BishopReal
import Sequence as BishopSequence
import RealProperties as BishopP
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as SeriesExt
import DASHI.Moonshine.AbelBishopFactorialComplexExpDiskExact as Factorial

realAxis : BishopReal.ℝ → Complex.BishopComplex
realAxis x = Complex.complex x BishopReal.0ℝ

realAxisPower :
  ∀ x n →
  Complex._≈C_
    (Algebra.powC (realAxis x) n)
    (realAxis (BishopReal.pow x n))
realAxisPower x zero =
  (let open BishopP.ℝ-Solver in
    solve 0
      (Κ 1ℚᵘ ⊜ Κ 1ℚᵘ)
      BishopP.≃-refl)
  ,
  (let open BishopP.ℝ-Solver in
    solve 0
      (Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
      BishopP.≃-refl)
realAxisPower x (suc n) =
  let
    previous = realAxisPower x n
    lifted =
      Algebra.mulCCongruent
        (Complex.≈C-refl (realAxis x))
        previous
    power = BishopReal.pow x n
    realStep :
      BishopReal._≃_
        (Complex.re
          (Algebra._*C_
            (realAxis x)
            (realAxis power)))
        (BishopReal.pow x (suc n))
    realStep =
      let open BishopP.ℝ-Solver in
      solve 2
        (λ v p →
          ((v ⊗ p) ⊖ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ))
          ⊜ (p ⊗ v))
        BishopP.≃-refl x power
    imagStep :
      BishopReal._≃_
        (Complex.im
          (Algebra._*C_
            (realAxis x)
            (realAxis power)))
        BishopReal.0ℝ
    imagStep =
      let open BishopP.ℝ-Solver in
      solve 2
        (λ v p →
          ((v ⊗ Κ 0ℚᵘ) ⊕ (Κ 0ℚᵘ ⊗ p))
          ⊜ Κ 0ℚᵘ)
        BishopP.≃-refl x power
  in
  (BishopP.≃-trans (proj₁ lifted) realStep)
  ,
  (BishopP.≃-trans (proj₂ lifted) imagStep)

realAxisFactorialPositiveTermReal :
  ∀ x n →
  BishopReal._≃_
    (Complex.re
      (Factorial.originalBishopFactorialExpPositiveTerm
        (realAxis x) n))
    (Exp.expTerm x (suc n))
realAxisFactorialPositiveTermReal x n =
  BishopP.≃-trans
    (BishopP.*-congˡ
      (proj₁ (realAxisPower x (suc n))))
    (BishopP.*-comm
      (Factorial.factorialCoefficient (suc n))
      (BishopReal.pow x (suc n)))

realAxisFactorialPositiveTermImagZero :
  ∀ x n →
  BishopReal._≃_
    (Complex.im
      (Factorial.originalBishopFactorialExpPositiveTerm
        (realAxis x) n))
    BishopReal.0ℝ
realAxisFactorialPositiveTermImagZero x n =
  BishopP.≃-trans
    (BishopP.*-congˡ
      (proj₂ (realAxisPower x (suc n))))
    (let open BishopP.ℝ-Solver
     in solve 1
       (λ a → a ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
       BishopP.≃-refl
       (Factorial.factorialCoefficient (suc n)))


------------------------------------------------------------------------
-- ALL-DEGREE same-source identity, including the constant term.
------------------------------------------------------------------------

originalBishopFactorialComplexTerm :
  Complex.BishopComplex → Nat → Complex.BishopComplex
originalBishopFactorialComplexTerm z n =
  Algebra.scaleC
    (Factorial.factorialCoefficient n)
    (Algebra.powC z n)

originalBishopFactorialComplexTermRealAxis :
  ∀ x n →
  Complex._≈C_
    (originalBishopFactorialComplexTerm (realAxis x) n)
    (realAxis (Exp.expTerm x n))
originalBishopFactorialComplexTermRealAxis x n =
  (BishopP.≃-trans
    (BishopP.*-congˡ (proj₁ (realAxisPower x n)))
    (BishopP.*-comm
      (Factorial.factorialCoefficient n)
      (BishopReal.pow x n)))
  ,
  (BishopP.≃-trans
    (BishopP.*-congˡ (proj₂ (realAxisPower x n)))
    (let open BishopP.ℝ-Solver
     in solve 1
       (λ a → a ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
       BishopP.≃-refl
       (Factorial.factorialCoefficient n)))

originalBishopPositiveTermIsFullSuccessor :
  ∀ z n →
  Factorial.originalBishopFactorialExpPositiveTerm z n
  ≡
  originalBishopFactorialComplexTerm z (suc n)
originalBishopPositiveTermIsFullSuccessor z n = refl


------------------------------------------------------------------------
-- ORIGINAL REAL EXPONENTIAL SERIES LIMIT: PAID BY POINTWISE EQUALITY
-- AND THE EXISTING VENDORED BISHOP CONVERGENCE TRANSFER.
--
-- Unlike the disk-valued complex exponential construction, this
-- convergence proof applies on the full real axis x : BishopReal.ℝ.
------------------------------------------------------------------------

originalBishopRealAxisFactorialPartialSameOriginal :
  ∀ x count →
  BishopReal._≃_
    (BishopSequence.SeriesOf
      (λ n → Complex.re
        (originalBishopFactorialComplexTerm (realAxis x) n))
      count)
    (BishopSequence.SeriesOf (Exp.expTerm x) count)
originalBishopRealAxisFactorialPartialSameOriginal x count =
  SeriesExt.seriesPartialSumsCongruent
    (λ n → proj₁ (originalBishopFactorialComplexTermRealAxis x n))
    count

originalBishopRealAxisFactorialSeriesConvergesToOriginalExp :
  ∀ x →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf
      (λ n → Complex.re
        (originalBishopFactorialComplexTerm (realAxis x) n)))
    (Exp.bishopExp x)
originalBishopRealAxisFactorialSeriesConvergesToOriginalExp x =
  BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc count-1) →
      BishopP.≃-symm
        (originalBishopRealAxisFactorialPartialSameOriginal
          x (suc count-1))})
    ( Exp.bishopExp x
    , Exp.bishopExpConverges x
    )
