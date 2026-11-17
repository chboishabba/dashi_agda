module DASHI.Physics.YangMills.YMClayOriginalRationalSU2ToBishopTraceExact where

------------------------------------------------------------------------
-- ORIGINAL native rational SU2 -> ACTUAL Bishop matrix trace map.
-- NO made-up rational scalar, no postulated cast from legacy real.
-- Uses the existing Data.Rational.Base.toℚᵘ normalization followed by
-- the pinned native Bishop rational embedding and concrete quaternion
-- 2×2 trace already constructed in YMClayBishopSU2QuaternionTraceWeldExact.
--
-- This establishes literal trace carrier alignment for EVERY original
-- RationalUnitQuaternion. It does NOT yet establish multiplicativity
-- of the map, nor norm-one transport from the rational source, NOR
-- original product Haar, continuous completion or a Clay mass gap.
--
-- Credit: original DASHI Balaban rational-SU2 and Bishop rational
-- normalization owners, Wilson/Balaban, Murray/Csimma and Bishop.
------------------------------------------------------------------------

import Data.Rational.Base as ℚ
import Real as B
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact
  as Original
import DASHI.Physics.YangMills.YMClayBishopSU2QuaternionTraceWeldExact
  as Q
import DASHI.Physics.YangMills.YMClayBishopSetoidFiniteAdjointTraceExact
  as Trace

-- The original RationalUnitQuaternion stores canonical reduced rationals.
-- Conversion to the ACTUAL vendor unnormalised scalar is selected by the
-- stdlib's toℚᵘ operation, not an invented semantic equality.
rationalCoordinateToBishop : ℚ.ℚ → B.ℝ
rationalCoordinateToBishop x = B._⋆ (ℚ.toℚᵘ x)

originalRationalQuaternionAsBishop :
  Original.RationalUnitQuaternion → Q.BishopQuaternion
originalRationalQuaternionAsBishop q =
  Q.quaternion
    (rationalCoordinateToBishop (Original.realPart q))
    (rationalCoordinateToBishop (Original.imagI q))
    (rationalCoordinateToBishop (Original.imagJ q))
    (rationalCoordinateToBishop (Original.imagK q))

-- The SAME original rational source realPart is the Bishop-normalised
-- real matrix trace. This uses the prior *proved arithmetic* half law.
originalSU2NormalizedBishopTrace :
  ∀ q →
  B._≃_
    (Trace.bishopNormalizedRealTrace 2 Q.bishopHalf
      (Q.quaternionMatrix (originalRationalQuaternionAsBishop q)))
    (rationalCoordinateToBishop (Original.realPart q))
originalSU2NormalizedBishopTrace q =
  Q.bishopQuaternionNormalizedTrace
    (originalRationalQuaternionAsBishop q)

-- The true missing next theorem is a *multiplicative* carrier homomorphism
-- plus norm-one transport and SU2 order/compactness on the Bishop side,
-- not another duplicate definition of the rational quaternion group.
