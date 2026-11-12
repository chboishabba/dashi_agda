module DASHI.Moonshine.AbelBishopInverseKoenigsShiftConvergenceExact where

------------------------------------------------------------------------
-- BISHOP INVERSE-KOENIGS: SUCCESSOR LIMIT IS THE SAME LIMIT.
--
-- This pays the specific reindexing seam used when passing
--      p * h_n(g(z)) ≈C h_(n+1)(z)
-- to a Schröder functional equation: one must know the entire
-- source sequence converges, not just a preferred subsequence.
--
-- The vendored Bishop Sequence.shift-is-subsequence and
-- xₙ⊆yₙ∧yₙ→y⇒xₙ→y provide the *actual Cauchy modulus* for the
-- +1 shift. No epsilon witness is postulated.
--
-- The endomap g, its selected inverse-branch domain and the actual
-- original Cauchy convergence of h remain separately unpaid.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product.Base using (_,_)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
import DASHI.Moonshine.AbelBishopInverseKoenigsFiniteOrbitExact as Orbit

originalBishopSuccessorConvergesToSame :
  (sequence : Nat → BishopReal.ℝ) →
  (limit : BishopReal.ℝ) →
  BishopSequence._ConvergesTo_ sequence limit →
  BishopSequence._ConvergesTo_
    (λ n → sequence (suc n))
    limit
originalBishopSuccessorConvergesToSame sequence limit converges =
  BishopSequence.xₙ⊆yₙ∧yₙ→y⇒xₙ→y
    (BishopSequence.shift-is-subsequence sequence (suc 0))
    (limit , converges)

originalBishopComplexSuccessorConvergesToSame :
  (sequence : Nat → Complex.BishopComplex) →
  (limit : Complex.BishopComplex) →
  Completion.OriginalBishopPointwiseComplexConverges sequence limit →
  Completion.OriginalBishopPointwiseComplexConverges
    (λ n → sequence (suc n)) limit
originalBishopComplexSuccessorConvergesToSame sequence limit converges =
  Completion.original-bishop-pointwise-complex-converges
    (originalBishopSuccessorConvergesToSame
      (λ n → Complex.re (sequence n))
      (Complex.re limit)
      (Completion.realConverges converges))
    (originalBishopSuccessorConvergesToSame
      (λ n → Complex.im (sequence n))
      (Complex.im limit)
      (Completion.imaginaryConverges converges))

originalBishopInverseKoenigsSuccessorConverges :
  (p : Complex.BishopComplex) →
  (g : Complex.BishopComplex → Complex.BishopComplex) →
  (z limit : Complex.BishopComplex) →
  Completion.OriginalBishopPointwiseComplexConverges
    (λ n → Orbit.inverseKoenigsPrefix p g n z) limit →
  Completion.OriginalBishopPointwiseComplexConverges
    (λ n → Orbit.inverseKoenigsPrefix p g (suc n) z) limit
originalBishopInverseKoenigsSuccessorConverges p g z limit converges =
  originalBishopComplexSuccessorConvergesToSame
    (λ n → Orbit.inverseKoenigsPrefix p g n z)
    limit converges
