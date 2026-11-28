module DASHI.Physics.YangMills.YMClayCMP102OriginalFinRowClosureExact where

------------------------------------------------------------------------
-- Section33: COMPLETE original CMP102 finite odd/even Fin-row source
-- weld from arbitrary-coefficient Bishop finite weighted Cauchy.
--
-- The earlier two row premises are now CONSTRUCTED from the general
-- original Bishop finite Cauchy power lemma, not assumed. The
-- previously originalGIsOriginalSignedCauchyTail conditional source
-- theorem becomes an UNCONDITIONAL all-count finite result.
--
-- All original CMP109 A/B factorial coefficients, original
-- Seq.SeriesOf count and signed original real X are preserved.
-- This is source-written, pending native Agda kernel/typecheck.
-- The quantitative Bishop order wing inequality and the separate
-- interacting 4D Wilson CMP116/OS/mass gap are not supplied here.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ; _/_)
import Real as R
import RealProperties as P
import DASHI.Foundations.BishopFiniteCauchyWeightedPowerExact as Weighted
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Physics.YangMills.YMClayCMP102OriginalEvenFinRecurrenceExact as Even
import DASHI.Physics.YangMills.YMClayCMP102OriginalOddFinRecurrenceExact as Odd
import DASHI.Physics.YangMills.YMClayCMP102OriginalOddEvenFinRowBIDIExact as Rows
import DASHI.Physics.YangMills.YMClayCMP102OriginalEndpointCauchyShiftExact as CMP102
import DASHI.Physics.YangMills.YMClayCMP102OriginalFiniteCauchyWingBoundsExact as Wing
import DASHI.Physics.YangMills.YMClayCMP102OriginalGToTailAlgebraExact as TailAlgebra
import DASHI.Physics.YangMills.YMClayCMP102OriginalFiniteTailGeometryExact as Tail
import DASHI.Physics.YangMills.YMClayCMP102OriginalGFiniteLimitTransportExact as Original

-- Exactly the original A coefficient convolution, with the one
-- required X-power, from generic native finite Cauchy theorem.
originalEvenWeightedCauchy : ∀ X → Even.EvenWeightedCauchy X
originalEvenWeightedCauchy X n =
  let
    q = Row.cauchyCoefficient
          CMP102.aCoefficient CMP102.aCoefficient n
    p = R.pow X n
    w = Row.cauchyCoefficient
          (Wing.aTerm X) (Wing.aTerm X) n
  in
  P.≃-trans
    (P.≃-symm (P.*-assoc q p X))
    (P.≃-trans
      (P.*-congʳ
        (Weighted.bishopFiniteWeightedCauchy
          CMP102.aCoefficient CMP102.aCoefficient X n))
      (P.*-comm w X))

-- Original B shifted by TWO powers from the same generic finite
-- identity; retains sign and BOTH singleton endpoint exceptions.
originalOddWeightedCauchy : ∀ X → Odd.OddWeightedCauchy X
originalOddWeightedCauchy X n =
  let
    q = Row.cauchyCoefficient
          CMP102.bCoefficient CMP102.bCoefficient n
    p = R.pow X n
    w = Row.cauchyCoefficient
          (Wing.bTerm X) (Wing.bTerm X) n
    open P.ℝ-Solver
  in
  P.≃-trans
    (solve 3
      (λ q p x →
        q ⊗ ((p ⊗ x) ⊗ x)
          ⊜ (q ⊗ p) ⊗ (x ⊗ x))
      P.≃-refl q p X)
    (P.≃-trans
      (P.*-congʳ
        (Weighted.bishopFiniteWeightedCauchy
          CMP102.bCoefficient CMP102.bCoefficient X n))
      (P.*-comm w (R._*_ X X)))

-- These are the actual TWO native row witnesses, no longer
-- parameters of the original consumer.
originalOddFinRowClosed : ∀ X n → Rows.originalOddFinRow X n
originalOddFinRowClosed X n =
  Odd.originalOddFinRowFromWeightedCauchy
    X n (originalOddWeightedCauchy X)

originalEvenFinRowClosed : ∀ X n → Rows.originalEvenFinRow X n
originalEvenFinRowClosed X n =
  Even.originalEvenRowFromWeightedCauchy
    X n (originalEvenWeightedCauchy X)

originalShiftedRowFinReindexClosed :
  ∀ X n → TailAlgebra.OriginalShiftedRowFinReindex X n
originalShiftedRowFinReindexClosed X n =
  Rows.originalShiftedRowFinReindexFromOriginalOddEven
    X n (originalOddFinRowClosed X n) (originalEvenFinRowClosed X n)

-- Mathematical scalar finiteness: each ORIGINAL G_(n+1) is exactly
-- its actual A/B signed Cauchy residual tail, with no remaining
-- Fin-reindex assumption, for ALL count n and ALL signed Bishop X.
originalGToActualCauchyTailClosed :
  ∀ X n →
  R._≃_
    (Original.originalGPrefix X (suc n))
    (Tail.originalSignedCauchyTail X n)
originalGToActualCauchyTailClosed X n =
  TailAlgebra.originalGIsOriginalSignedCauchyTail
    X n (originalShiftedRowFinReindexClosed X n)
