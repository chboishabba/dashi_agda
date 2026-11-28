module DASHI.Physics.YangMills.YMClayCMP102OriginalFiniteTailToLimitExact where

------------------------------------------------------------------------
-- Section 33 original scalar Bishop analytic consumer, no alternate
-- series and no original G(X)=0 premise. All original finite algebra
-- is now sourced from the unconditional finite odd/even closure.
--
-- The last quantitative leaf is the true native Bishop magnitude
-- order of the ACTUAL original signed Cauchy tail.
-- The finite zero-count case is kept separate rather than smuggling
-- a false all-count tail formula (G_0=1, no A/B terms).
--
-- No postulates. Source-written, pending pinned Agda kernel.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ; _/_)
import Real as R
import RealProperties as P

import DASHI.Physics.YangMills.YMClayCMP102OriginalFinRowClosureExact as Closed
import DASHI.Physics.YangMills.YMClayCMP102OriginalEndpointCauchyShiftExact as CMP102
import DASHI.Physics.YangMills.YMClayCMP102OriginalFiniteTailGeometryExact as Tail
import DASHI.Physics.YangMills.YMClayCMP102OriginalGFiniteLimitTransportExact as Original
import DASHI.Physics.YangMills.YMClayCMP102OriginalGeometricSqueezeReceiverExact as Rate
import DASHI.Physics.YangMills.YMClayCMP102OriginalAbsoluteRateReceiverExact as Receiver
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half

-- This is EXACTLY the remaining native source finite Bishop-order
-- majorant, not a replacement absolute polynomial or an arbitrary
-- scalar numerical tolerance.
OriginalPositiveTailOrder : R.ℝ → Set
OriginalPositiveTailOrder X =
  ∀ n →
    R._≤_
      (R.∣ R._-_ (Tail.originalSignedCauchyTail X n) R.0ℝ ∣)
      (R.∣ Rate.originalGeometricRate (suc n) ∣)

-- Original count ZERO has G_0=1. Explicit genuine source terminal
-- obligation, not accidentally covered by the c>=1 Cauchy tail.
OriginalZeroCountOrder : R.ℝ → Set
OriginalZeroCountOrder X =
  R._≤_
    (R.∣ R._-_ (Original.originalGPrefix X zero) R.0ℝ ∣)
    (R.∣ Rate.originalGeometricRate zero ∣)

-- Every positive original count uses the now-closed original
-- Fin-reindex theorem, so the only remaining hypothesis is a
-- positive-tail order bound on existing Bishop finite terms.
originalAbsoluteRateFromPositiveTailOrder :
  ∀ X → OriginalZeroCountOrder X →
  OriginalPositiveTailOrder X →
  Receiver.originalAbsoluteRateBound X
originalAbsoluteRateFromPositiveTailOrder X hzero htail zero = hzero
originalAbsoluteRateFromPositiveTailOrder X hzero htail (suc n) =
  P.≤-respˡ-≃
    (P.∣-∣-cong
      (P.+-cong
        (Closed.originalGToActualCauchyTailClosed X n)
        (P.-‿cong P.≃-refl)))
    (htail n)

-- Finite source geometric order => ORIGINAL represented CMP109 G=0.
-- No new convergence theorem is introduced: use the source native
-- vanishingDifferenceConvergenceExact absolute receiver.
originalGZeroFromActualFiniteTailOrder :
  ∀ X (inside : R._≤_ (R.∣ X ∣) Half.bishopQuarter) →
  OriginalZeroCountOrder X →
  OriginalPositiveTailOrder X →
  R._≃_ (Original.originalG X inside) R.0ℝ
originalGZeroFromActualFiniteTailOrder X inside hzero htail =
  Receiver.originalGZeroFromAbsoluteRate
    X inside
    (originalAbsoluteRateFromPositiveTailOrder X hzero htail)


-- The exceptional original empty SeriesOf prefix has A_0=B_0=0.
-- Consequently G_0(X)=1 for ALL signed original Bishop X, not a
-- Cauchy wing. This is actual five-term source ring algebra.
originalGZeroCountIsOne : ∀ X →
  R._≃_ (Original.originalGPrefix X zero) R.1ℝ
originalGZeroCountIsOne X =
  let
    two = CMP102.two
    open P.ℝ-Solver
  in solve 2
    (λ x t →
       (((Κ 1ℚᵘ ⊕ (⊝ (t ⊗ Κ 0ℚᵘ)))
          ⊕ (⊝ (x ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ))))
          ⊕ ((t ⊗ x) ⊗ Κ 0ℚᵘ))
          ⊕ ((x ⊗ x) ⊗ (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ))
       ⊜ Κ 1ℚᵘ)
    P.≃-refl X two
