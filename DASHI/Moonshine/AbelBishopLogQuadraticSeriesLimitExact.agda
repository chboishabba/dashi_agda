module DASHI.Moonshine.AbelBishopLogQuadraticSeriesLimitExact where

------------------------------------------------------------------------
-- CANONICAL LOG(1+w) QUADRATIC REMAINDER: ACTUAL BISHOP LIMIT.
--
-- Reuses literal logarithm terms, already-proved absolute series
-- convergence on the Bishop unit disk, the exact finite prefix/tail
-- split and the vendored successor-subsequence convergence theorem.
--
-- For every original witness normSq(w) ~= ratio^2, 0<=ratio<1,
-- the genuine shifted source series (degree >=2) converges to
--
--    originalCanonicalLogOnePlus(w) -C w.
--
-- This does NOT assume a principal branch or prove a numerical norm
-- bound on the remainder. The remaining selected local analytic gate
-- is the source square-tail comparison and chart identification.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexConstantMultiplicationConvergenceExact as Continuity
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
import DASHI.Moonshine.AbelBishopInverseKoenigsShiftConvergenceExact as Shift
import DASHI.Moonshine.AbelBishopInverseKoenigsRemainderFactorExact as Ring
import DASHI.Moonshine.AbelBishopLogOnePlusCoefficientDominationExact as LogConvergence
import DASHI.Moonshine.AbelBishopLogQuadraticFiniteTailExact as Finite

logQuadraticCanonicalRemainder :
  ∀ {w ratio} →
  Unit.BishopUnitIntervalRatio ratio →
  BishopReal._≃_ (Norm.normSqC w) (Norm.square ratio) →
  Complex.BishopComplex
logQuadraticCanonicalRemainder {w} interval norm =
  Algebra._-C_
    (LogConvergence.originalBishopLogOnePlusCanonicalLimitOnUnitDisk
      interval norm)
    w

-- (w + tail) - w = tail on the actual componentwise Bishop carrier.
originalBishopComplexRemoveFirstSummand :
  ∀ w tail →
  Complex._≈C_
    (Algebra._-C_ (Algebra._+C_ w tail) w)
    tail
originalBishopComplexRemoveFirstSummand
  (Complex.complex a b) (Complex.complex c d) =
  (let open BishopP.ℝ-Solver in
   solve 2
     (λ w t → (w ⊕ t) ⊖ w ⊜ t)
     BishopP.≃-refl a c)
  ,
  (let open BishopP.ℝ-Solver in
   solve 2
     (λ w t → (w ⊕ t) ⊖ w ⊜ t)
     BishopP.≃-refl b d)

originalBishopLogPrefixMinusFirstIsQuadraticTail :
  ∀ w n →
  Complex._≈C_
    (Algebra._-C_
      (Finite.originalBishopLogFinitePrefix w (suc n)) w)
    (Finite.originalBishopLogQuadraticTailPrefix w n)
originalBishopLogPrefixMinusFirstIsQuadraticTail w n =
  Ring.complexTrans
    (Algebra.subCCongruent
      (Finite.originalBishopLogFiniteQuadraticDecomposition w n)
      (Complex.≈C-refl w))
    (originalBishopComplexRemoveFirstSummand
      w (Finite.originalBishopLogQuadraticTailPrefix w n))

originalBishopLogFullPrefixConverges :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (norm : BishopReal._≃_ (Norm.normSqC w) (Norm.square ratio)) →
  Completion.OriginalBishopPointwiseComplexConverges
    (Finite.originalBishopLogFinitePrefix w)
    (LogConvergence.originalBishopLogOnePlusCanonicalLimitOnUnitDisk
      interval norm)
originalBishopLogFullPrefixConverges interval norm =
  let source =
        LogConvergence.originalBishopLogOnePlusCanonicalLimitConvergesOnUnitDisk
          interval norm
  in
  Completion.original-bishop-pointwise-complex-converges
    (Complex.realConverges source)
    (Complex.imagConverges source)

originalBishopLogQuadraticTailConverges :
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (norm : BishopReal._≃_ (Norm.normSqC w) (Norm.square ratio)) →
  Completion.OriginalBishopPointwiseComplexConverges
    (Finite.originalBishopLogQuadraticTailPrefix w)
    (logQuadraticCanonicalRemainder interval norm)
originalBishopLogQuadraticTailConverges {w} interval norm =
  let
    full = Finite.originalBishopLogFinitePrefix w
    value =
      LogConvergence.originalBishopLogOnePlusCanonicalLimitOnUnitDisk
        interval norm
    shifted =
      Shift.originalBishopComplexSuccessorConvergesToSame
        full value
        (originalBishopLogFullPrefixConverges interval norm)

    realMinus =
      Continuity.originalBishopSubtractConverges
        (λ n → Complex.re (full (suc n)))
        (λ n → Complex.re w)
        (Complex.re value) (Complex.re w)
        (Completion.realConverges shifted)
        (Continuity.originalBishopConstantSequenceConverges
          (Complex.re w))

    imagMinus =
      Continuity.originalBishopSubtractConverges
        (λ n → Complex.im (full (suc n)))
        (λ n → Complex.im w)
        (Complex.im value) (Complex.im w)
        (Completion.imaginaryConverges shifted)
        (Continuity.originalBishopConstantSequenceConverges
          (Complex.im w))
  in
  Completion.original-bishop-pointwise-complex-converges
    (BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ n →
        proj₁ (originalBishopLogPrefixMinusFirstIsQuadraticTail w n))
      (Complex.re (logQuadraticCanonicalRemainder interval norm) ,
        realMinus))
    (BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ n →
        proj₂ (originalBishopLogPrefixMinusFirstIsQuadraticTail w n))
      (Complex.im (logQuadraticCanonicalRemainder interval norm) ,
        imagMinus))
