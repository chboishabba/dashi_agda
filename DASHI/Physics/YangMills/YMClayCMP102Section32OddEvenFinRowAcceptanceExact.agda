module DASHI.Physics.YangMills.YMClayCMP102Section32OddEvenFinRowAcceptanceExact where

------------------------------------------------------------------------
-- Original CMP102 native typecheck root for signed two-source
-- finite row decomposition, and the original G-to-wing consumer.
-- Both odd/even row witnesses are explicitly unfilled proof INPUTS,
-- never postulated or obtained from the desired G=0 theorem.
-- Agda 2.9 + transitive --safe graph pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
import Real as R
import DASHI.Physics.YangMills.YMClayCMP102OriginalOddEvenFinRowBIDIExact as Rows
import DASHI.Physics.YangMills.YMClayCMP102OriginalSignedTriangleZeroExact as Signed
import DASHI.Physics.YangMills.YMClayCMP102OriginalGToTailAlgebraExact as Tail
import DASHI.Physics.YangMills.YMClayCMP102OriginalFiniteTailGeometryExact as Geometry
import DASHI.Physics.YangMills.YMClayCMP102OriginalGFiniteLimitTransportExact as Original

originalFiniteSignedRowDifference : ∀ X count →
  R._≃_ (Signed.originalSignedTriangle X count)
    (R._-_ (Rows.originalOddFinite X count)
           (Rows.originalEvenFinite X count))
originalFiniteSignedRowDifference = Rows.originalSignedTriangleOddMinusEven

originalFiniteOddEvenToTail :
  ∀ X n →
  Rows.originalOddFinRow X n →
  Rows.originalEvenFinRow X n →
  R._≃_ (Original.originalGPrefix X (suc n))
    (Geometry.originalSignedCauchyTail X n)
originalFiniteOddEvenToTail = Rows.originalGIsCauchyTailFromNativeOddEven
