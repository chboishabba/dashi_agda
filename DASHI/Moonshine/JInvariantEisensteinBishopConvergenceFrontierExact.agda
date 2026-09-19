module DASHI.Moonshine.JInvariantEisensteinBishopConvergenceFrontierExact where

------------------------------------------------------------------------
-- EISENSTEIN q-SERIES: EXACT BISHOP / SAME-CARRIER CONVERGENCE FRONTIER
--
-- DASHI CONTRIBUTION / REPO CROSS-POLLINATION
--
-- This owner sharpens the old blanket
--
--   finite truncation -> infinite analytic Eisenstein series
--
-- debt by reusing the convergence and q-decay machinery already checked or
-- source-written in this repository.
--
-- Two convergence routes are kept distinct rather than conflated:
--
--   A. Bishop setoid route
--      vendored Bishop SeriesOf + absolute convergence + componentwise complex
--      limits.  Its remaining application seam is still a weld to the older
--      propositional-equality `ConcreteComplex` evaluator.
--
--   B. same-ConcreteComplex route
--      the literal finite E4/E6 truncation sequences are already compiled to
--      same-carrier limits from explicit componentwise Cauchy evidence.  This
--      route avoids the Bishop carrier weld, but still needs the quantitative
--      Cauchy/majorant proof.
--
-- Since the previous frontier, the finite coefficient side is also sharper:
--
--   sigma_3(n) <= n^4,
--   sigma_5(n) <= n^6
--
-- are owned on the internal divisor kernel.  The literal q producer now has a
-- principal-strip modulus compiler and an upper-half-plane decay compiler:
-- given explicit nondegenerate order/branch evidence,
--
--   Im(tau)>0 -> |q(tau)|<1.
--
-- The generic compiler is paid; inhabiting those order/branch inputs on a
-- selected ordinary analytic package is not silently inferred from the bare
-- ConstructedOrderedCompleteReal interface.
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
import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumBoundExact as PowerBound
import DASHI.Moonshine.JInvariantEisensteinSameCarrierLimitCompilerExact as SameCarrier
import DASHI.Moonshine.JInvariantEisensteinTruncationIncrementExact as Increment
import DASHI.Moonshine.JInvariantEisensteinIncrementCoefficientBoundExact as IncrementBound
import DASHI.Moonshine.JInvariantQPrincipalStripModulusExact as QModulus
import DASHI.Moonshine.JInvariantQUpperHalfPlaneDecayCompilerExact as QDecay

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
    concreteMurrayBishopSetoidBackendOwned : Bool

    sameCarrierConcreteComplexLimitCompilerOwned : Bool
    eisensteinCoefficientPolynomialGrowthOwned : Bool
    literalTruncationIncrementIdentityOwned : Bool
    literalIncrementCoefficientEnvelopeOwned : Bool
    qPowerModulusPropagationCompilerOwned : Bool
    polynomialGeometricIncrementModulusCompilerOwned : Bool
    genericDominatedTailCompilerOwned : Bool
    genericTailToCauchyBridgeOwned : Bool
    selectedTailToCauchyBridgeInhabited : Bool
    fastCauchyLegacyQuotientInterfaceWeldOwned : Bool
    concreteLegacyQuotientInhabited : Bool
    sameCarrierModulusAlgebraInhabited : Bool
    principalStripQModulusCompilerOwned : Bool
    upperHalfPlaneQDecayCompilerOwned : Bool
    concreteQOrderAndStripInputsOwned : Bool

    -- This is specifically the Bishop-setoid -> legacy ConcreteComplex weld.
    -- The same-carrier route above avoids needing it.
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
    true true true true true true
    true true true true true true true true false true false false true true false
    false
    false false false false
    false false
    "The nondegenerate Murray-Bishop setoid ordered-complete backend is concrete and its Cauchy completeness is already owned. The shortest literal-q route still stays on the existing ConcreteComplex carrier: same-carrier Cauchy completion is paid, sigma3/sigma5 polynomial growth is paid, the exact E4/E6 successor increments and their 240/504 coefficient envelopes are paid; q-power modulus propagation and polynomial-times-geometric increment-modulus compilers are also paid. Generic dominated-tail vanishing and generic tail-to-IsCauchy bridge surfaces are now paid in Analysis. The old Fast-Cauchy quotient realization is also welded definition-for-definition into the newer backend quotient seam, while an actual concrete legacy quotient / selected tail-to-Cauchy inhabitant remains unpaid. Their ordinary modulus multiplication/triangle/order package remains an explicit same-carrier inhabitant, and principal-strip/upper-half-plane q-decay compilers remain paid conditionally. The genuine remaining inputs are a nondegenerate ordinary order/polar-branch inhabitant, the concrete polynomial-times-geometric E4/E6 Cauchy majorants, and the limit = analytic lattice-sum same-object theorem."
