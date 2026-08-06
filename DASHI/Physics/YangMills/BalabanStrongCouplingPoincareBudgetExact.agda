module DASHI.Physics.YangMills.BalabanStrongCouplingPoincareBudgetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
--
-- SOURCE FORMULAS
--
-- Under their positive Bakry--Emery constant K_S, the infinite-volume measure
-- satisfies
--
--   Ent(F^2) <= (2/K_S) E(F,F),
--   Var(F)   <= (1/K_S) E(F,F).
--
-- Poincare gives temporal L2 semigroup decay, while spatial exponential
-- covariance decay additionally uses derivative-generator commutator estimates
-- and the Guionnet--Zegarlinski propagation argument.  Poincare alone is not
-- silently promoted to spatial clustering here.
--
-- DASHI CONTRIBUTION
--
-- Close the exact coefficient algebra downstream of a supplied inverse law for
-- K_S, including the log-Sobolev/Poincare factor two and the two-observable
-- covariance-square budget produced by Poincare plus Cauchy--Schwarz.  At the
-- concrete SU(2), d=4, |beta|=1/96 interior point, K_S=1/2, hence the exact
-- Poincare and log-Sobolev coefficients are 2 and 4.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _-_; _*_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.YangMills.BalabanStrongCouplingSUFourDimensionalMarginExact as Strong

poincareCoefficient : ℚ → ℚ
poincareCoefficient inverseCurvature = inverseCurvature

logSobolevCoefficient : ℚ → ℚ
logSobolevCoefficient inverseCurvature =
  (+ 2 / 1) * inverseCurvature

logSobolevIsTwicePoincare :
  ∀ inverseCurvature →
  logSobolevCoefficient inverseCurvature
  ≡ (+ 2 / 1) * poincareCoefficient inverseCurvature
logSobolevIsTwicePoincare inverseCurvature =
  solve (inverseCurvature ∷ [])

poincareVarianceBudget : ℚ → ℚ → ℚ
poincareVarianceBudget inverseCurvature dirichletEnergy =
  inverseCurvature * dirichletEnergy

poincareCovarianceSquareBudget : ℚ → ℚ → ℚ → ℚ
poincareCovarianceSquareBudget
    inverseCurvature leftEnergy rightEnergy =
  (inverseCurvature * inverseCurvature)
    * (leftEnergy * rightEnergy)

covarianceSquareBudgetFactorsThroughVariances :
  ∀ inverseCurvature leftEnergy rightEnergy →
  poincareCovarianceSquareBudget
    inverseCurvature leftEnergy rightEnergy
  ≡ poincareVarianceBudget inverseCurvature leftEnergy
    * poincareVarianceBudget inverseCurvature rightEnergy
covarianceSquareBudgetFactorsThroughVariances
    inverseCurvature leftEnergy rightEnergy =
  solve (inverseCurvature ∷ leftEnergy ∷ rightEnergy ∷ [])

curvatureInverseCancelsPoincareBudget :
  ∀ curvature inverseCurvature dirichletEnergy →
  inverseCurvature * curvature ≡ 1ℚ →
  curvature
    * poincareVarianceBudget inverseCurvature dirichletEnergy
  ≡ dirichletEnergy
curvatureInverseCancelsPoincareBudget
    curvature inverseCurvature dirichletEnergy inverseLaw
  rewrite inverseLaw =
  solve (curvature ∷ inverseCurvature ∷ dirichletEnergy ∷ [])

configuredSU2Curvature : ℚ
configuredSU2Curvature =
  Strong.paperSUCurvatureConstant
    (+ 2 / 1)
    Strong.configuredInteriorBeta

configuredSU2InverseCurvature : ℚ
configuredSU2InverseCurvature = + 2 / 1

configuredSU2InverseLaw :
  configuredSU2InverseCurvature * configuredSU2Curvature ≡ 1ℚ
configuredSU2InverseLaw = solve []

configuredSU2PoincareCoefficientExact :
  poincareCoefficient configuredSU2InverseCurvature ≡ + 2 / 1
configuredSU2PoincareCoefficientExact = solve []

configuredSU2LogSobolevCoefficientExact :
  logSobolevCoefficient configuredSU2InverseCurvature ≡ + 4 / 1
configuredSU2LogSobolevCoefficientExact = solve []

record FunctionalInequalitySpatialDecayBoundary : Set where
  constructor functionalInequalitySpatialDecayBoundary
  field
    poincareInequalityEstablished : Set
    derivativeGeneratorCommutatorBoundEstablished : Set
    finiteSpeedDerivativePropagationEstablished : Set
    guionnetZegarlinskiSpatialDecayStepEstablished : Set
    exponentialSpatialCovarianceDecayEstablished : Set

-- The record deliberately has no constructor exported from a bare Poincare
-- coefficient.  The published mass-gap proof uses all of the spatial
-- propagation ingredients, not Poincare in isolation.
