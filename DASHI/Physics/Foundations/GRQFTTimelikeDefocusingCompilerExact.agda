{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTTimelikeDefocusingCompilerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Cut
import DASHI.Physics.Foundations.CMP119SymmetricStressComponentReductionExact as Sym
import DASHI.Physics.Foundations.GRQFTNegativeActiveStressRepulsionRouteExact as Active

------------------------------------------------------------------------
-- 4D EINSTEIN TRACE-REVERSAL COMPILER
--
-- Convention:
--   metric signature (-,+,+,+)
--   local orthonormal comoving frame u=(1,0,0,0)
--   Lambda = 0
--   normalized kappa = 1
--
-- For a diagonal stress tensor,
--
--   T = -rho + p_x + p_y + p_z
--   R_00 = kappa * (T_00 - (1/2) g_00 T)
--
-- and with g_00=-1 this becomes
--
--   R_00 = (1/2) (rho + p_x + p_y + p_z).
--
-- Thus the active-stress combination from the previous cut feeds the timelike
-- Ricci contraction directly.
------------------------------------------------------------------------

half : ℚ
half = Int.+ 1 / 2

minusOne : ℚ
minusOne = - 1ℚ

normalizedKappa : ℚ
normalizedKappa = 1ℚ

normalizedLambda : ℚ
normalizedLambda = 0ℚ

stressTraceRestFrame :
  Cut.RationalTensor4 → ℚ
stressTraceRestFrame tensor =
  - (tensor Flat.timeAxis Flat.timeAxis)
  + tensor Flat.xAxis Flat.xAxis
  + tensor Flat.yAxis Flat.yAxis
  + tensor Flat.zAxis Flat.zAxis

ricci00TraceReversed :
  Cut.RationalTensor4 → ℚ
ricci00TraceReversed tensor =
  normalizedKappa *
    (tensor Flat.timeAxis Flat.timeAxis
      - half * minusOne * stressTraceRestFrame tensor)
  + normalizedLambda * minusOne

finiteGRStressTraceIsNegativeFour :
  stressTraceRestFrame Cut.finiteGRStressRational ≡ - (Int.+ 4 / 1)
finiteGRStressTraceIsNegativeFour = solve []

finiteGRRicci00IsNegativeOne :
  ricci00TraceReversed Cut.finiteGRStressRational ≡ minusOne
finiteGRRicci00IsNegativeOne = solve []

ricci00EqualsHalfActiveStressOnFiniteTarget :
  ricci00TraceReversed Cut.finiteGRStressRational
    ≡ half * Active.activeStressSum Cut.finiteGRStressRational
ricci00EqualsHalfActiveStressOnFiniteTarget = solve []

------------------------------------------------------------------------
-- RAYCHAUDHURI SIGN COMPILER
--
-- Timelike Raychaudhuri in 3+1 dimensions:
--
--   d theta / d tau
--     = -(1/3) theta^2 - sigma^2 + omega^2 - R_mn u^m u^n.
--
-- We isolate the curvature contribution first.  A negative timelike Ricci
-- contraction contributes positively to expansion evolution.
------------------------------------------------------------------------

raychaudhuriCurvatureContribution :
  ℚ → ℚ
raychaudhuriCurvatureContribution ricciUU = - ricciUU

finiteGRCurvatureContributionIsPositiveOne :
  raychaudhuriCurvatureContribution
    (ricci00TraceReversed Cut.finiteGRStressRational)
  ≡ 1ℚ
finiteGRCurvatureContributionIsPositiveOne = solve []

third : ℚ
third = Int.+ 1 / 3

raychaudhuriRHS :
  (thetaSquared shearSquared vorticitySquared ricciUU : ℚ) → ℚ
raychaudhuriRHS thetaSquared shearSquared vorticitySquared ricciUU =
  - (third * thetaSquared)
  - shearSquared
  + vorticitySquared
  - ricciUU

finiteGRInitiallyParallelShearFreeIrrotationalRaychaudhuri :
  raychaudhuriRHS
    0ℚ
    0ℚ
    0ℚ
    (ricci00TraceReversed Cut.finiteGRStressRational)
  ≡ 1ℚ
finiteGRInitiallyParallelShearFreeIrrotationalRaychaudhuri = solve []

------------------------------------------------------------------------
-- CMP119 TRANSPORT
--
-- Ten symmetric component payments already imply the four diagonal values.
-- Therefore they also imply the same trace, active-stress, timelike-Ricci, and
-- curvature-defocusing diagnostics.
------------------------------------------------------------------------

cmp119StressTraceRestFrame :
  ∀ {StressTensor : Set} →
  (evaluator : Cut.CMP119RationalStressComponentEvaluator StressTensor) →
  StressTensor →
  ℚ
cmp119StressTraceRestFrame evaluator stress =
  - (Cut.component evaluator stress Flat.timeAxis Flat.timeAxis)
  + Cut.component evaluator stress Flat.xAxis Flat.xAxis
  + Cut.component evaluator stress Flat.yAxis Flat.yAxis
  + Cut.component evaluator stress Flat.zAxis Flat.zAxis

cmp119Ricci00TraceReversed :
  ∀ {StressTensor : Set} →
  (evaluator : Cut.CMP119RationalStressComponentEvaluator StressTensor) →
  StressTensor →
  ℚ
cmp119Ricci00TraceReversed evaluator stress =
  normalizedKappa *
    (Cut.component evaluator stress Flat.timeAxis Flat.timeAxis
      - half * minusOne * cmp119StressTraceRestFrame evaluator stress)
  + normalizedLambda * minusOne

tenComponentsCompileToNegativeRicci00 :
  ∀ {StressTensor : Set}
    {evaluator : Cut.CMP119RationalStressComponentEvaluator StressTensor}
    {stress : StressTensor} →
  Sym.NormalizedSymmetricTenComponentInstance evaluator stress →
  cmp119Ricci00TraceReversed evaluator stress ≡ minusOne
tenComponentsCompileToNegativeRicci00 instance
  rewrite Sym.qft00 instance
        | Sym.qft11 instance
        | Sym.qft22 instance
        | Sym.qft33 instance
  = refl

tenComponentsCompileToPositiveCurvatureDefocusing :
  ∀ {StressTensor : Set}
    {evaluator : Cut.CMP119RationalStressComponentEvaluator StressTensor}
    {stress : StressTensor} →
  Sym.NormalizedSymmetricTenComponentInstance evaluator stress →
  raychaudhuriCurvatureContribution
    (cmp119Ricci00TraceReversed evaluator stress)
  ≡ 1ℚ
tenComponentsCompileToPositiveCurvatureDefocusing instance
  rewrite tenComponentsCompileToNegativeRicci00 instance
  = refl

tenComponentsCompileToPositiveInitialRaychaudhuriRHS :
  ∀ {StressTensor : Set}
    {evaluator : Cut.CMP119RationalStressComponentEvaluator StressTensor}
    {stress : StressTensor} →
  Sym.NormalizedSymmetricTenComponentInstance evaluator stress →
  raychaudhuriRHS
    0ℚ
    0ℚ
    0ℚ
    (cmp119Ricci00TraceReversed evaluator stress)
  ≡ 1ℚ
tenComponentsCompileToPositiveInitialRaychaudhuriRHS instance
  rewrite tenComponentsCompileToNegativeRicci00 instance
  = refl

------------------------------------------------------------------------
-- WHAT HAS ACTUALLY BEEN PROVED
------------------------------------------------------------------------

data TimelikeDefocusingStatus : Set where
  negativeTimelikeRicci : TimelikeDefocusingStatus
  positiveRaychaudhuriCurvatureContribution : TimelikeDefocusingStatus
  positiveInitialExpansionDerivativeUnderZeroKinematicTerms :
    TimelikeDefocusingStatus

finiteGRDefocusingStatus :
  TimelikeDefocusingStatus
finiteGRDefocusingStatus =
  positiveInitialExpansionDerivativeUnderZeroKinematicTerms

record TimelikeDefocusingBoundary : Set where
  constructor timelike-defocusing-boundary
  field
    finiteTargetTraceReverseGivesNegativeRicciUU : Bool
    negativeRicciUUGivesPositiveRaychaudhuriCurvatureTerm : Bool
    zeroInitialExpansionShearVorticityGivesPositiveExpansionDerivative : Bool
    resultRequiresNegativeNewtonG : Bool
    resultRequiresNegativeInertialMass : Bool
    localDefocusingContributionEqualsGlobalOutwardTrajectory : Bool
    solvedBoundaryValueGeometryStillRequiredForRemoteAcceleration : Bool
    cmp119TenComponentsTransportWholeSignChain : Bool

canonicalTimelikeDefocusingBoundary :
  TimelikeDefocusingBoundary
canonicalTimelikeDefocusingBoundary =
  timelike-defocusing-boundary
    true true true false false false true true
