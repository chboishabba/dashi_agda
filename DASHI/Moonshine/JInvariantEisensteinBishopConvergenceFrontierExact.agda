module DASHI.Moonshine.JInvariantEisensteinBishopConvergenceFrontierExact where

------------------------------------------------------------------------
-- EISENSTEIN q-SERIES: EXACT BISHOP CONVERGENCE FRONTIER
--
-- DASHI CONTRIBUTION / REPO CROSS-POLLINATION
--
-- This owner sharpens the old blanket
--
--   finite truncation -> infinite analytic Eisenstein series
--
-- debt by reusing the convergence machinery that is already checked and
-- vendored in this repository.  In particular, DASHI already owns:
--
--   * the Bishop/Murray real carrier and Sequence.SeriesOf;
--   * Cauchy completeness and uniqueness of limits;
--   * absolute-series convergence -> convergence;
--   * the stdlib finite-sum <-> Bishop SeriesOf prefix bridge.
--
-- What remains is therefore NOT a missing completeness theorem.  For the
-- actual E4/E6 route we still need:
--
--   1. a componentwise convergence carrier for the constructed complex used
--      by JInvariantEisensteinFiniteQSeriesExact;
--   2. concrete absolute-convergence/majorant proofs for
--        240 sigma_3(n) q^n and -504 sigma_5(n) q^n, |q| < 1;
--   3. a same-object theorem identifying the resulting q-series limits with
--      the analytic lattice-sum EisensteinSeries object.
--
-- SOURCE / CODE ATTRIBUTION
--
-- Errett Bishop and Douglas Bridges, Constructive Analysis, Springer, 1985.
-- DOI: 10.1007/978-3-642-61667-9.
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant",
-- Dalhousie University BSc Honours thesis, 2022, arXiv:2205.08354.
-- No DOI was assigned to the thesis.
--
-- Code continuation: Viktor Csimma, viktorcsimma/bishop, pinned by DASHI at
-- vendor/bishop commit 240e38c7f6938f20f865b1f956c5f084da48bd54.
--
-- The decomposition and adapters below are DASHI contributions.  None of the
-- above citations is treated as importing proof authority by itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import Real as BishopReal
import RealProperties as BishopProperties
import Sequence as BishopSequence

import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bishop
import DASHI.Foundations.BishopFinSumSeriesBridgeExact as FinSum

------------------------------------------------------------------------
-- Canonical aliases to the already-owned checked Bishop convergence engine.
------------------------------------------------------------------------

bishopSeriesLimit :
  (terms : Nat -> BishopReal.ℝ) ->
  Bishop.BishopAbsoluteSeriesConvergent terms ->
  BishopReal.ℝ
bishopSeriesLimit = Bishop.bishopSeriesLimit

bishopSeriesLimitConvergence :
  (terms : Nat -> BishopReal.ℝ) ->
  (absolute : Bishop.BishopAbsoluteSeriesConvergent terms) ->
  Bishop.BishopConvergesTo
    (BishopSequence.SeriesOf terms)
    (bishopSeriesLimit terms absolute)
bishopSeriesLimitConvergence = Bishop.bishopSeriesLimitConvergence

finitePrefixMatchesBishopSeries :
  (terms : Nat -> BishopReal.ℝ) ->
  (count : Nat) ->
  BishopReal._≃_
    (FinSum.finSum terms count)
    (BishopSequence.SeriesOf terms count)
finitePrefixMatchesBishopSeries = FinSum.finSumIsSeriesOf

record BishopAbsoluteSeriesLimitReceipt
    (terms : Nat -> BishopReal.ℝ) : Set where
  constructor bishop-absolute-series-limit-receipt
  field
    absoluteConvergence : Bishop.BishopAbsoluteSeriesConvergent terms
    limit : BishopReal.ℝ
    canonicalLimit : BishopReal._≃_ limit (bishopSeriesLimit terms absoluteConvergence)
    convergesToLimit :
      Bishop.BishopConvergesTo (BishopSequence.SeriesOf terms) limit

open BishopAbsoluteSeriesLimitReceipt public

compileAbsoluteSeriesLimit :
  (terms : Nat -> BishopReal.ℝ) ->
  (absolute : Bishop.BishopAbsoluteSeriesConvergent terms) ->
  BishopAbsoluteSeriesLimitReceipt terms
compileAbsoluteSeriesLimit terms absolute =
  bishop-absolute-series-limit-receipt
    absolute
    (bishopSeriesLimit terms absolute)
    BishopProperties.≃-refl
    (bishopSeriesLimitConvergence terms absolute)

------------------------------------------------------------------------
-- Exact residual frontier.
--
-- Keep these booleans descriptive.  In particular, the finite E4/E6 evaluator
-- is on ConcreteComplex.ComplexPair over ConstructiveRealSpine, while the
-- theorem above is the native Bishop real/setoid SeriesOf backend.  We do not
-- identify those carriers merely because both are constructive analysis.
------------------------------------------------------------------------

record EisensteinBishopConvergenceFrontier : Set where
  constructor eisenstein-bishop-convergence-frontier
  field
    vendoredBishopBackendOwned : Bool
    finiteSumToBishopSeriesBridgeOwned : Bool
    absoluteConvergenceToLimitCompilerOwned : Bool
    bishopLimitUniquenessOwned : Bool

    constructedComplexComponentwiseConvergenceOwned : Bool
    e4ConcreteAbsoluteConvergenceOwned : Bool
    e6ConcreteAbsoluteConvergenceOwned : Bool
    bishopLimitEqualsAnalyticLatticeEisenstein : Bool
    analyticKleinJPromotionOwned : Bool

    citationsCreateProofAuthority : Bool
    finitePythonParityCreatesConvergence : Bool
    reading : String

open EisensteinBishopConvergenceFrontier public

canonicalEisensteinBishopConvergenceFrontier :
  EisensteinBishopConvergenceFrontier
canonicalEisensteinBishopConvergenceFrontier =
  eisenstein-bishop-convergence-frontier
    true true true true
    false false false false false
    false false
    "Bishop completeness is already paid: any real term sequence with a checked absolute-convergence witness has a canonical convergent SeriesOf limit, and finite stdlib sums agree with its prefixes. The remaining Eisenstein debt is the actual constructed-complex lift, concrete E4/E6 majorants for |q|<1, and the q-series-limit = analytic lattice-sum same-object theorem; citations and Python parity do not pay those obligations."
