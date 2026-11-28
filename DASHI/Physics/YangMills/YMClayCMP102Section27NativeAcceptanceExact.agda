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
import DASHI.Physics.YangMills.YMClayCMP102OriginalAbsoluteRateReceiverExact as Abs
import DASHI.Physics.YangMills.YMClayCMP102OriginalFiniteCauchyWingBoundsExact as Wing
import DASHI.Physics.YangMills.YMClayCMP102OriginalSignedTriangleZeroExact as Triangle
import DASHI.Physics.YangMills.YMClayCMP102OriginalFiniteTailGeometryExact as Tail

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

-- Section 30: direct ONE-absolute-bound receiver on the same original
-- Bishop represented finite source (no independent lower/upper brackets).
originalFiniteAbsoluteErrorConverges :
  ∀ X → Abs.originalAbsoluteRateBound X →
  Seq._ConvergesTo_ (Original.originalGPrefix X) R.0ℝ
originalFiniteAbsoluteErrorConverges =
  Abs.originalGPrefixZeroFromAbsoluteRate

-- Section 30 original physical-signed coefficient histories: the
-- imported finite native Bishop triangle and Cauchy wing are actual
-- all-count values, not synthetic abstract finite coefficient data.
originalFiniteAPrefixAbsoluteBound = Wing.originalAPrefixAbsoluteBound
originalFiniteBPrefixAbsoluteBound = Wing.originalBPrefixAbsoluteBound
originalFiniteASquareWingAbsoluteBound =
  Wing.originalASquareCauchyWingFiniteBound
originalFiniteBSquareWingAbsoluteBound =
  Wing.originalBSquareCauchyWingFiniteBound

-- Section 30: all-degree original signed Cauchy source vanishing,
-- its literal Bishop polynomial triangle, and the original physical
-- A/B square rectangles used by the finite wing bound.
originalSignedPolynomialTriangleZero :
  ∀ X count →
  R._≃_ (Triangle.originalSignedTriangle X count) R.0ℝ
originalSignedPolynomialTriangleZero =
  Triangle.originalSignedTriangleZero

originalActualASquareTailRectangle =
  Tail.originalASquareIsTailRectangle
originalActualBSquareTailRectangle =
  Tail.originalBSquareIsTailRectangle
