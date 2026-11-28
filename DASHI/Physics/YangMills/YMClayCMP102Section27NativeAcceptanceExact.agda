module DASHI.Physics.YangMills.YMClayCMP102Section27NativeAcceptanceExact where

------------------------------------------------------------------------
-- Source-native Agda 2.9 acceptance entrypoint, intentionally imports
-- BOTH the original CMP102 five-term Bishop polynomial factorization
-- and the original geometric Bishop squeeze -> original G zero receiver.
-- These source modules are written but NOT YET TYPECHECKED.
-- No Cauchy-family replacement, no second series, no postulate.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.YMClayCMP102OriginalGFiniteLimitTransportExact as Original
import DASHI.Physics.YangMills.YMClayCMP102OriginalGPrefixSignedSquaresBIDIExact as Algebra
import DASHI.Physics.YangMills.YMClayCMP102OriginalGeometricSqueezeReceiverExact as Rate

open import Agda.Builtin.Nat using (Nat)
import Real as R
import Sequence as Seq

-- Static same-source owner references, forcing names and imports to
-- resolve under native Agda, not separate syntactic grep acceptance.
originalFiniteGFactorization : ∀ X (count : Nat) →
  R._≃_ (Original.originalGPrefix X count)
    (Algebra.originalSignedSquares X count)
originalFiniteGFactorization = Algebra.originalGPrefixSignedSquares

originalFiniteRateZero :
  Seq._ConvergesTo_ Rate.originalGeometricRate R.0ℝ
originalFiniteRateZero = Rate.originalGeometricRateZero
