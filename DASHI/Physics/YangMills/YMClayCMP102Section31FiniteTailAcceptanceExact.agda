module DASHI.Physics.YangMills.YMClayCMP102Section31FiniteTailAcceptanceExact where

-- SOURCE-WRITTEN / PENDING Agda 2.9 KERNEL.
-- One actual original G-prefix, exact finite A/B source,
-- explicit remaining finite row-reindex obligation.
-- No postulate, no alternate series and no claim G=0.

open import Agda.Builtin.Nat using (Nat; suc)
import Real as R
import DASHI.Physics.YangMills.YMClayCMP102OriginalGFiniteLimitTransportExact as Original
import DASHI.Physics.YangMills.YMClayCMP102OriginalSignedTriangleZeroExact as Signed
import DASHI.Physics.YangMills.YMClayCMP102OriginalFiniteTailGeometryExact as Tail
import DASHI.Physics.YangMills.YMClayCMP102OriginalGToTailAlgebraExact as Weld

originalGToSourceNormal : ∀ X n →
  R._≃_
    (Original.originalGPrefix X (suc n))
    (R._+_ (Weld.originalShiftedRowNormal X n)
           (Weld.originalRawSquareWingTail X n))
originalGToSourceNormal = Weld.originalGIsSourceNormalPlusRawWings

originalGToExactCauchyTail :
  ∀ X n → Weld.OriginalShiftedRowFinReindex X n →
  R._≃_
    (Original.originalGPrefix X (suc n))
    (Tail.originalSignedCauchyTail X n)
originalGToExactCauchyTail =
  Weld.originalGIsOriginalSignedCauchyTail

originalSignedTriangleZero :
  ∀ X n → R._≃_ (Signed.originalSignedTriangle X n) R.0ℝ
originalSignedTriangleZero = Signed.originalSignedTriangleZero
