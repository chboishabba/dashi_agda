module DASHI.Moonshine.AbelBishopKoenigsIncrementSeriesExact where

------------------------------------------------------------------------
-- KOENIGS INCREMENTS: ACTUAL VENDORED BISHOP SERIES COMPLETION
--
-- Native Bishop/Murray absolute-series and Cauchy proofs establish
-- convergence of signed increment prefixes componentwise.
-- The application still owes absolute convergence of its actual increments.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import Sequence as BishopSequence
import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bishop
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion

originalBishopKoenigsIncrementPrefix :
  (increments : Nat → Complex.BishopComplex) →
  Nat → Complex.BishopComplex
originalBishopKoenigsIncrementPrefix increments n =
  Complex.complex
    (BishopSequence.SeriesOf (Complex.realTerms increments) n)
    (BishopSequence.SeriesOf (Complex.imagTerms increments) n)

originalBishopKoenigsFiniteTailToCauchy :
  (increments : Nat → Complex.BishopComplex) →
  Complex.ComponentwiseAbsoluteSeriesConvergent increments →
  Completion.OriginalBishopComplexCauchy
    (originalBishopKoenigsIncrementPrefix increments)
originalBishopKoenigsFiniteTailToCauchy increments absolute =
  Completion.original-bishop-complex-cauchy
    (Bishop.bishopConvergentImpliesCauchy
      (Bishop.bishopAbsoluteSeriesConverges
        (Complex.realAbsolute absolute)))
    (Bishop.bishopConvergentImpliesCauchy
      (Bishop.bishopAbsoluteSeriesConverges
        (Complex.imagAbsolute absolute)))

originalBishopKoenigsIncrementLimit :
  (increments : Nat → Complex.BishopComplex) →
  Complex.ComponentwiseAbsoluteSeriesConvergent increments →
  Complex.BishopComplex
originalBishopKoenigsIncrementLimit increments absolute =
  Completion.originalBishopComplexCauchyLimit
    (originalBishopKoenigsIncrementPrefix increments)
    (originalBishopKoenigsFiniteTailToCauchy increments absolute)

originalBishopKoenigsIncrementLimitConverges :
  (increments : Nat → Complex.BishopComplex) →
  (absolute : Complex.ComponentwiseAbsoluteSeriesConvergent increments) →
  Completion.OriginalBishopPointwiseComplexConverges
    (originalBishopKoenigsIncrementPrefix increments)
    (originalBishopKoenigsIncrementLimit increments absolute)
originalBishopKoenigsIncrementLimitConverges increments absolute =
  Completion.originalBishopComplexCauchyConverges
    (originalBishopKoenigsIncrementPrefix increments)
    (originalBishopKoenigsFiniteTailToCauchy increments absolute)

originalBishopKoenigsIncrementLimitUnique :
  (increments : Nat → Complex.BishopComplex) →
  (absolute : Complex.ComponentwiseAbsoluteSeriesConvergent increments) →
  (other : Complex.BishopComplex) →
  Completion.OriginalBishopPointwiseComplexConverges
    (originalBishopKoenigsIncrementPrefix increments) other →
  Complex._≈C_
    (originalBishopKoenigsIncrementLimit increments absolute)
    other
originalBishopKoenigsIncrementLimitUnique increments absolute other proof =
  Completion.originalBishopComplexCauchyLimitUnique
    (originalBishopKoenigsIncrementPrefix increments)
    (originalBishopKoenigsFiniteTailToCauchy increments absolute)
    other proof
