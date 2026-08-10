module DASHI.Physics.Closure.NSTriadKNCertifiedOwnerReserveOptimizationRound37Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- Round 36 represented the owner constraints as a feasible region and
-- distinguished robust/critical/infeasible geometries.  The continuation
-- analysis proposed the sharper diagnostic
--
--   Delta_* = 1 - inf_{eta feasible} sum_i eta_i.
--
-- We do not postulate an infimum or optimizer.  Instead this module gives the
-- exact constructive substitute: a `CertifiedEtaMinimizer` is an actual
-- feasible point whose total eta is <= every other feasible point.
--
-- Its reserve
--
--   1 - etaTotal(minimizer)
--
-- is >= the reserve of every feasible competitor.  If its total is < 1 then
-- a strict absorbing allocation exists.  Conversely, if its total is >= 1,
-- no feasible allocation can have strict reserve.  This makes the owner
-- architecture falsifiable as soon as physical producer constraints become
-- concrete, without manufacturing a real-analysis optimization theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 1ℚ; _-_; _≤_; _<_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNNineOwnerRobustReservePolytopeRound36Exact as Reserve

record CertifiedEtaMinimizer
    {parameterLevel}
    (polytope : Reserve.AdmissibleBudgetPolytope parameterLevel) :
    Set parameterLevel where
  field
    minimizer : Reserve.Parameter polytope
    minimizerFeasible : Reserve.Feasible polytope minimizer
    globallyMinimalEta :
      ∀ point →
      Reserve.Feasible polytope point →
      Reserve.etaTotal polytope minimizer
      ≤ Reserve.etaTotal polytope point

open CertifiedEtaMinimizer public

reserveAt :
  ∀ {parameterLevel}
    (polytope : Reserve.AdmissibleBudgetPolytope parameterLevel) →
  Reserve.Parameter polytope → ℚ
reserveAt polytope point = 1ℚ - Reserve.etaTotal polytope point

certifiedMinimizerMaximizesReserve :
  ∀ {parameterLevel}
    {polytope : Reserve.AdmissibleBudgetPolytope parameterLevel} →
  (certificate : CertifiedEtaMinimizer polytope) →
  ∀ point → Reserve.Feasible polytope point →
  reserveAt polytope point ≤ reserveAt polytope (minimizer certificate)
certifiedMinimizerMaximizesReserve {polytope = polytope}
    certificate point feasible =
  ℚP.+-monoʳ-≤ 1ℚ
    (ℚP.neg-antimono-≤
      (globallyMinimalEta certificate point feasible))

record StrictCertifiedReserve
    {parameterLevel}
    {polytope : Reserve.AdmissibleBudgetPolytope parameterLevel}
    (certificate : CertifiedEtaMinimizer polytope) : Set parameterLevel where
  field
    optimalTotalBelowOne :
      Reserve.etaTotal polytope (minimizer certificate) < 1ℚ

open StrictCertifiedReserve public

NoStrictFeasibleReserve :
  ∀ {parameterLevel} →
  Reserve.AdmissibleBudgetPolytope parameterLevel → Set parameterLevel
NoStrictFeasibleReserve polytope =
  ∀ point →
  Reserve.Feasible polytope point →
  1ℚ ≤ Reserve.etaTotal polytope point

certifiedMinimumAtOrAboveOneRulesOutStrictReserve :
  ∀ {parameterLevel}
    {polytope : Reserve.AdmissibleBudgetPolytope parameterLevel} →
  (certificate : CertifiedEtaMinimizer polytope) →
  1ℚ ≤ Reserve.etaTotal polytope (minimizer certificate) →
  NoStrictFeasibleReserve polytope
certifiedMinimumAtOrAboveOneRulesOutStrictReserve
    certificate oneBelowMinimum point feasible =
  ℚP.≤-trans
    oneBelowMinimum
    (globallyMinimalEta certificate point feasible)

record CriticalCertifiedMinimum
    {parameterLevel}
    {polytope : Reserve.AdmissibleBudgetPolytope parameterLevel}
    (certificate : CertifiedEtaMinimizer polytope) : Set parameterLevel where
  field
    optimalTotalExactlyOne :
      Reserve.etaTotal polytope (minimizer certificate) ≡ 1ℚ

open CriticalCertifiedMinimum public

criticalCertifiedMinimumRulesOutStrictReserve :
  ∀ {parameterLevel}
    {polytope : Reserve.AdmissibleBudgetPolytope parameterLevel}
    {certificate : CertifiedEtaMinimizer polytope} →
  CriticalCertifiedMinimum certificate →
  NoStrictFeasibleReserve polytope
criticalCertifiedMinimumRulesOutStrictReserve
    {certificate = certificate} critical =
  certifiedMinimumAtOrAboveOneRulesOutStrictReserve
    certificate
    (rewriteOne (optimalTotalExactlyOne critical))
  where
  rewriteOne : ∀ {value : ℚ} → value ≡ 1ℚ → 1ℚ ≤ value
  rewriteOne refl = ℚP.≤-refl

certifiedOwnerReserveOptimizationTyped : Bool
certifiedOwnerReserveOptimizationTyped = true

physicalCertifiedNineOwnerMinimizerConstructed : Bool
physicalCertifiedNineOwnerMinimizerConstructed = false

certifiedOwnerReserveOptimizationTypedIsTrue :
  certifiedOwnerReserveOptimizationTyped ≡ true
certifiedOwnerReserveOptimizationTypedIsTrue = refl

physicalCertifiedNineOwnerMinimizerConstructedIsFalse :
  physicalCertifiedNineOwnerMinimizerConstructed ≡ false
physicalCertifiedNineOwnerMinimizerConstructedIsFalse = refl
