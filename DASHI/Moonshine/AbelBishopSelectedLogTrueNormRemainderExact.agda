module DASHI.Moonshine.AbelBishopSelectedLogTrueNormRemainderExact where

------------------------------------------------------------------------
-- ORIGINAL SELECTED P-CHART: TRUE-NORM QUADRATIC LOG REMAINDER.
--
-- Instantiate the nontrivial FINITE->BISHOP-LIMIT P1.L theorem on the
-- ACTUAL p^-1*t chart with the selected original quantitative disk:
--
--   N(p) >= (27/20)^2,  N(t) <= (1/10)^2,
--   N(p^-1*t) <= (2/27)^2.
--
-- The source log limit is literally
--   selectedOriginalLogQuadraticTailLimit p nz t pLower tInside
-- from the earlier original-series convergence proof.
--
-- The conclusion retains its true modulus ||p^-1*t||:
--
--   || R2(p^-1*t) ||
--      <= (1/2) * ||p^-1*t||^2 / (1-||p^-1*t||).
--
-- No selected radius equality, invented principal Log, new source
-- limit or generic analytic-root axiom. The R4 square-root calculus
-- is the existing explicit STILL UNINHABITED input. The final
-- (8/27)*N(t) bound further requires the two native reciprocal-order
-- comparisons for N(p) and 1-||p^-1*t||.
--
-- SOURCE-WRITTEN; actual Agda 2.9 kernel receipt pending.
------------------------------------------------------------------------

import Real as BishopReal

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal
import DASHI.Physics.YangMills.BalabanP33BishopR4ChordMetricFromSquareRootExact as R4
import DASHI.Moonshine.AbelBishopSelectedLogAffineReconstructionExact as Affine
import DASHI.Moonshine.AbelBishopSelectedLocalLogDiskAdmissionExact as Selected
import DASHI.Moonshine.AbelBishopSelectedLogUpperDiskQuadraticTailExact as Tail
import DASHI.Moonshine.AbelBishopLogQuadraticTrueNormFiniteMajorantExact as Majorant
import DASHI.Moonshine.AbelBishopLogQuadraticTrueNormLimitOrderExact as Limit

-- The ACTUAL selected original shifted-log SERIES limit, with no
-- replacement by a chosen analytic germ or a proof-record field.
originalSelectedTrueNormRemainder :
  (roots : R4.BishopSquareRootCalculus) →
  ∀ p (nz : Reciprocal.BishopComplexNonzero p) t →
  (pLower :
    BishopReal._≤_
      (Norm.square Selected.selectedLowerModulus)
      (Norm.normSqC p)) →
  (tInside :
    BishopReal._≤_
      (Norm.normSqC t)
      (Norm.square Selected.selectedLogRadius)) →
  let
    w = Affine.normalizedDisplacement p nz t
    disk = Tail.selectedOriginalNormalizedLogUpperDisk
      p nz t pLower tInside
    inside = Limit.originalBishopTrueNormBelowOneFromDisk
      roots Selected.selectedLogRelativeInterval disk
  in BishopReal._≤_
    (Majorant.trueBishopRadius roots
      (Tail.selectedOriginalLogQuadraticTailLimit
        p nz t pLower tInside))
    (Limit.originalBishopSharpQuadraticValue roots w inside)
originalSelectedTrueNormRemainder roots p nz t pLower tInside =
  Limit.originalBishopUpperDiskLogQuadraticTrueNormBound
    roots
    Selected.selectedLogRelativeInterval
    (Tail.selectedOriginalNormalizedLogUpperDisk
      p nz t pLower tInside)
