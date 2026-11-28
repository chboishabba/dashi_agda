module DASHI.Physics.YangMills.YMClayCMP102Section33WeightedCauchyClosureAcceptanceExact where

------------------------------------------------------------------------
-- Original CMP102 native source admission root:
-- arbitrary-coefficient Bishop weighted finite Cauchy equality
--  -> original A/B weighted Cauchy
--  -> all-count even and odd original Fin row
--  -> original shifted row reindex WITHOUT an input
--  -> exact ORIGINAL finite five-term G to A/B signed Cauchy tail.
--
-- No postulates, no substitute series or G=0 assumption.
-- Pinned Agda 2.9, Bishop vendor and --safe graph NOT YET RUN.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
import Real as R
import DASHI.Foundations.BishopFiniteCauchyWeightedPowerExact as Weighted
import DASHI.Physics.YangMills.YMClayCMP102OriginalFinRowClosureExact as Closed
import DASHI.Physics.YangMills.YMClayCMP102OriginalOddEvenFinRowBIDIExact as Rows
import DASHI.Physics.YangMills.YMClayCMP102OriginalGToTailAlgebraExact as Algebra
import DASHI.Physics.YangMills.YMClayCMP102OriginalFiniteTailGeometryExact as Tail
import DASHI.Physics.YangMills.YMClayCMP102OriginalGFiniteLimitTransportExact as Original

originalNativeWeightedCauchy =
  Weighted.bishopFiniteWeightedCauchy

originalNativeOddFinRow : ∀ X n → Rows.originalOddFinRow X n
originalNativeOddFinRow = Closed.originalOddFinRowClosed

originalNativeEvenFinRow : ∀ X n → Rows.originalEvenFinRow X n
originalNativeEvenFinRow = Closed.originalEvenFinRowClosed

originalNativeShiftedRowClosed :
  ∀ X n → Algebra.OriginalShiftedRowFinReindex X n
originalNativeShiftedRowClosed =
  Closed.originalShiftedRowFinReindexClosed

originalNativeFiniteGIsSourceTail :
  ∀ X n →
  R._≃_
    (Original.originalGPrefix X (suc n))
    (Tail.originalSignedCauchyTail X n)
originalNativeFiniteGIsSourceTail =
  Closed.originalGToActualCauchyTailClosed
