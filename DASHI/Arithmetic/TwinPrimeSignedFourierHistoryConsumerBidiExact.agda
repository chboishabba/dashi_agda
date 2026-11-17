{-# OPTIONS --safe #-}
module DASHI.Arithmetic.TwinPrimeSignedFourierHistoryConsumerBidiExact where

-- Reuses original DASHI residual / period codec owners; does not duplicate
-- the historical fibre from the Pickover PR #1260.
-- Any *specified* signed shell consumer is exactly preserved by the
-- Nat <-> (period, Fin270) history-aware coding. No positivity follows.
-- Source-written; Agda kernel receipt pending.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
import DASHI.Arithmetic.TwinPrimeNat270PeriodResidualBidiExact as Period
import DASHI.Arithmetic.TwinPrimeResidualMangoldtBidiExact as Bidi

-- A signed frequency-shell consumer has a scalar type and a concrete
-- function of the original Nat; this surface does not manufacture a
-- Fourier analytic estimate, real logarithms, or an FFT implementation.
record SignedShellConsumer : Set₁ where
  field
    Scalar : Set
    shellReadout : Nat → Scalar
open SignedShellConsumer public

shellAtRetainedPeriod :
  (C : SignedShellConsumer) →
  Period.NatPeriod270 → Scalar C
shellAtRetainedPeriod C =
  Bidi.liftNatConsumer (shellReadout C)

shellHistoryForward :
  (C : SignedShellConsumer) (n : Nat) →
  shellAtRetainedPeriod C (Period.encodeNatPeriod270 n)
    ≡ shellReadout C n
shellHistoryForward C = Bidi.liftConsumerSound (shellReadout C)

shellHistoryBackward :
  (C : SignedShellConsumer) (code : Period.NatPeriod270) →
  shellReadout C (Period.decodeNatPeriod270 code)
    ≡ shellAtRetainedPeriod C code
shellHistoryBackward C code = Bidi.liftConsumerComplete (shellReadout C) code

-- To obtain Hardy-Littlewood asymptotics, instantiate shellReadout
-- with the *actual signed arithmetic Fourier contribution* and prove
-- a bound on the signed sum. This transport does not prove that bound.
