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
-- vendored in this repository. DASHI owns the Bishop/Murray real carrier,
-- Sequence.SeriesOf, completeness/limit uniqueness, absolute -> ordinary
-- convergence, the finite-sum -> SeriesOf bridge, and now a componentwise
-- Bishop-complex series compiler.
--
-- What remains for the actual E4/E6 route is therefore narrower:
--
--   1. weld the Bishop setoid-complex convergence carrier to the older
--      ConcreteComplex.ComplexPair evaluator used by the finite recurrence;
--   2. prove concrete absolute-convergence/majorant bounds for
--        240 sigma_3(n) q^n and -504 sigma_5(n) q^n, |q| < 1;
--   3. identify the resulting q-series limits with the analytic lattice-sum
--      EisensteinSeries object.
--
-- SOURCE / CODE ATTRIBUTION
-- Errett Bishop and Douglas Bridges, Constructive Analysis, Springer, 1985,
-- DOI 10.1007/978-3-642-61667-9.
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant",
-- Dalhousie University BSc Honours thesis, 2022, arXiv:2205.08354; no DOI.
-- Viktor Csimma's continuation is pinned by DASHI at vendor/bishop commit
-- 240e38c7f6938f20f865b1f956c5f084da48bd54.
--
-- The decomposition and adapters below are DASHI contributions. Citations do
-- not import proof authority by themselves.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import Real as BishopReal
import RealProperties as BishopProperties
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as BishopComplex
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

compileComponentwiseComplexLimit :
  (terms : Nat -> BishopComplex.BishopComplex) ->
  (absolute : BishopComplex.ComponentwiseAbsoluteSeriesConvergent terms) ->
  BishopComplex.ComplexSeriesConvergesTo
    terms
    (BishopComplex.complexSeriesLimit terms absolute)
compileComponentwiseComplexLimit = BishopComplex.complexSeriesLimitConvergence

------------------------------------------------------------------------
-- Exact residual frontier.
------------------------------------------------------------------------

record EisensteinBishopConvergenceFrontier : Set where
  constructor eisenstein-bishop-convergence-frontier
  field
    vendoredBishopBackendOwned : Bool
    finiteSumToBishopSeriesBridgeOwned : Bool
    absoluteConvergenceToLimitCompilerOwned : Bool
    bishopLimitUniquenessOwned : Bool
    bishopComplexComponentwiseConvergenceOwned : Bool

    constructedComplexEvaluatorCarrierWeldOwned : Bool
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
    true true true true true
    false false false false false
    false false
    "Bishop completeness and generic componentwise complex convergence are paid. The remaining Eisenstein debt is the carrier weld to the existing ConcreteComplex finite evaluator, concrete E4/E6 absolute-convergence majorants for |q|<1, and the q-series-limit = analytic lattice-sum same-object theorem; citations and Python parity do not pay those obligations."
