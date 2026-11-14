module DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact where

------------------------------------------------------------------------
-- VENDORED BISHOP / MURRAY CAUCHY COMPLETENESS: EXACT COMPLEX LIFT
--
-- Reuse, do not postulate:
--  Real / Sequence (vendored Bishop), via
--  DASHI.Foundations.BishopConstructiveRealBridgeExact.
--  DASHI.Analysis.BishopComplexSeriesConvergenceExact owns the
--  literal Bishop complex pair and componentwise setoid equality.
--
-- This closes the COMPLETENESS step of Koenigs: two genuine Bishop
-- Cauchy component sequences determine one Bishop complex limit.
-- It DOES NOT prove the Koenigs iterates are Cauchy or holomorphic.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_,_; proj₁; proj₂)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bishop
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex

record OriginalBishopComplexCauchy
    (trajectory : Nat → Complex.BishopComplex) : Set where
  constructor original-bishop-complex-cauchy
  field
    realCauchy :
      Bishop.BishopCauchy (λ n → Complex.re (trajectory n))
    imaginaryCauchy :
      Bishop.BishopCauchy (λ n → Complex.im (trajectory n))

open OriginalBishopComplexCauchy public

originalBishopComplexCauchyLimit :
  (trajectory : Nat → Complex.BishopComplex) →
  OriginalBishopComplexCauchy trajectory →
  Complex.BishopComplex
originalBishopComplexCauchyLimit trajectory cauchy =
  Complex.complex
    (BishopSequence.lim
      (Bishop.bishopCauchyComplete (realCauchy cauchy)))
    (BishopSequence.lim
      (Bishop.bishopCauchyComplete (imaginaryCauchy cauchy)))

record OriginalBishopPointwiseComplexConverges
    (trajectory : Nat → Complex.BishopComplex)
    (limit : Complex.BishopComplex) : Set where
  constructor original-bishop-pointwise-complex-converges
  field
    realConverges :
      Bishop.BishopConvergesTo
        (λ n → Complex.re (trajectory n))
        (Complex.re limit)
    imaginaryConverges :
      Bishop.BishopConvergesTo
        (λ n → Complex.im (trajectory n))
        (Complex.im limit)

open OriginalBishopPointwiseComplexConverges public

originalBishopComplexCauchyConverges :
  (trajectory : Nat → Complex.BishopComplex) →
  (cauchy : OriginalBishopComplexCauchy trajectory) →
  OriginalBishopPointwiseComplexConverges
    trajectory (originalBishopComplexCauchyLimit trajectory cauchy)
originalBishopComplexCauchyConverges trajectory cauchy =
  original-bishop-pointwise-complex-converges
    (proj₂ (Bishop.bishopCauchyComplete (realCauchy cauchy)))
    (proj₂ (Bishop.bishopCauchyComplete (imaginaryCauchy cauchy)))

originalBishopComplexCauchyLimitUnique :
  (trajectory : Nat → Complex.BishopComplex) →
  (cauchy : OriginalBishopComplexCauchy trajectory) →
  (other : Complex.BishopComplex) →
  OriginalBishopPointwiseComplexConverges trajectory other →
  Complex._≈C_
    (originalBishopComplexCauchyLimit trajectory cauchy)
    other
originalBishopComplexCauchyLimitUnique trajectory cauchy other converges =
  Bishop.bishopLimitUnique
    (realConverges
      (originalBishopComplexCauchyConverges trajectory cauchy))
    (realConverges converges)
  ,
  Bishop.bishopLimitUnique
    (imaginaryConverges
      (originalBishopComplexCauchyConverges trajectory cauchy))
    (imaginaryConverges converges)

-- No generic field/multiplier is fabricated here. The caller must supply
-- the ACTUAL original Bishop complex Koenigs trajectory, and establish its
-- two Cauchy component witnesses from geometric increment majorants.
originalBishopKoenigsLimitFromCauchy :
  (koenigs : Nat → Complex.BishopComplex) →
  OriginalBishopComplexCauchy koenigs →
  Complex.BishopComplex
originalBishopKoenigsLimitFromCauchy =
  originalBishopComplexCauchyLimit

originalBishopKoenigsLimitConverges :
  (koenigs : Nat → Complex.BishopComplex) →
  (cauchy : OriginalBishopComplexCauchy koenigs) →
  OriginalBishopPointwiseComplexConverges
    koenigs (originalBishopKoenigsLimitFromCauchy koenigs cauchy)
originalBishopKoenigsLimitConverges =
  originalBishopComplexCauchyConverges
