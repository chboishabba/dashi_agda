module DASHI.Analysis.BishopMachinSignedFiniteHistoryExact where

------------------------------------------------------------------------
-- K04a: CONCRETE FINITE BISHOP HISTORY FOR MACHIN'S SIGNED SERIES
--
-- Original analytic sources: John Machin (1706); Errett Bishop and
-- Douglas Bridges, Constructive Analysis (1985), DOI
-- 10.1007/978-3-642-61667-9; Zachary Murray, Constructive Analysis
-- in the Agda Proof Assistant (2022), arXiv:2205.08354.
--
-- SOURCE-REUSE / EXACT SCOPE
--   BishopMachinArctanConstructionExact owns the genuine convergent
--   Bishop atan signed terms and the constructed real bishopMachinPi.
--   BishopFiniteSeriesDifferenceExact owns finite SeriesOf subtraction.
-- This source derives the actual signed finite-stage series identity,
-- NOT a new Bishop carrier, a rational q_n embedding, an explicit
-- convergence modulus, trigonometric pi equality or analytic zeta.
-- Newly source-written; Agda kernel check pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Real as Bishop
import RealProperties as BishopP
import Sequence as Series

import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Foundations.BishopFiniteSeriesDifferenceExact as Difference

-- Preserve the original source terms and source-specific 16/4 factors,
-- including their true alternating sign. No new FRACTRAN term codec.
machinFifthWeightedTerm : Nat → Bishop.ℝ
machinFifthWeightedTerm n =
  Bishop._*_
    (Bishop._⋆ Machin.sixteen)
    (Machin.atanSignedTerm Machin.bishopOneFifth n)

machin239WeightedTerm : Nat → Bishop.ℝ
machin239WeightedTerm n =
  Bishop._*_
    (Bishop._⋆ Machin.four)
    (Machin.atanSignedTerm Machin.bishopOneTwoHundredThirtyNinth n)

machinSignedTerm : Nat → Bishop.ℝ
machinSignedTerm n =
  Bishop._-_ (machinFifthWeightedTerm n) (machin239WeightedTerm n)

-- This is the ACTUAL finite Bishop series on the source carrier.
machinSignedPartialStage : Nat → Bishop.ℝ
machinSignedPartialStage = Series.SeriesOf machinSignedTerm

machinFifthPartialStage : Nat → Bishop.ℝ
machinFifthPartialStage = Series.SeriesOf machinFifthWeightedTerm

machin239PartialStage : Nat → Bishop.ℝ
machin239PartialStage = Series.SeriesOf machin239WeightedTerm

-- Exact for every n, using the already proved finite-series
-- subtraction identity; no limit, continuity or numeric claim.
machinSignedPartialIsOriginalDifference :
  (n : Nat) →
  Bishop._≃_
    (machinSignedPartialStage n)
    (Bishop._-_
      (machinFifthPartialStage n)
      (machin239PartialStage n))
machinSignedPartialIsOriginalDifference n =
  BishopP.≃-symm
    (Difference.finiteSeriesDifference
      machinFifthWeightedTerm machin239WeightedTerm n)
