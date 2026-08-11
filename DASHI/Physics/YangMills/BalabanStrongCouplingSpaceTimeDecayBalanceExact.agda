module DASHI.Physics.YangMills.BalabanStrongCouplingSpaceTimeDecayBalanceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
--
-- Alice Guionnet and Boguslaw Zegarlinski,
-- "Lectures on Logarithmic Sobolev Inequalities",
-- Seminaire de Probabilites XXXVI, Lecture Notes in Mathematics 1801.
-- DOI: 10.1007/978-3-540-36107-7_1.
--
-- DASHI CONTRIBUTION
--
-- Isolate the exact optimization algebra behind converting temporal semigroup
-- decay plus finite-speed derivative propagation into spatial decay.  Suppose
-- the two competing exponents are
--
--   temporal = 2 K t,
--   spatial  = c (r - v t).
--
-- With D = 2K + cv and invD*D=1, choosing
--
--   t_* = invD c r
--
-- makes the exponents equal, with common value
--
--   invD (2 K c r).
--
-- The published proof supplies analytic semigroup, commutator and propagation
-- estimates.  This module closes their balancing algebra without pretending to
-- supply those estimates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _-_; _*_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

decayDenominator : ℚ → ℚ → ℚ → ℚ
decayDenominator curvature spatialRate propagationSpeed =
  (+ 2 / 1) * curvature + spatialRate * propagationSpeed

balancedTime : ℚ → ℚ → ℚ → ℚ
balancedTime inverseDenominator spatialRate distance =
  inverseDenominator * spatialRate * distance

temporalExponent : ℚ → ℚ → ℚ
temporalExponent curvature time =
  (+ 2 / 1) * curvature * time

spatialExponent : ℚ → ℚ → ℚ → ℚ → ℚ
spatialExponent spatialRate distance propagationSpeed time =
  spatialRate * (distance - propagationSpeed * time)

commonBalancedExponent : ℚ → ℚ → ℚ → ℚ
commonBalancedExponent curvature spatialRate distance inverseDenominator =
  inverseDenominator
    * ((+ 2 / 1) * curvature * spatialRate * distance)

balancedTemporalExponentExact :
  ∀ curvature spatialRate propagationSpeed distance inverseDenominator →
  temporalExponent curvature
    (balancedTime inverseDenominator spatialRate distance)
  ≡ commonBalancedExponent
      curvature spatialRate distance inverseDenominator
balancedTemporalExponentExact
    curvature spatialRate propagationSpeed distance inverseDenominator =
  solve
    (curvature ∷ spatialRate ∷ propagationSpeed ∷
     distance ∷ inverseDenominator ∷ [])

balancedSpatialDecompositionExact :
  ∀ curvature spatialRate propagationSpeed distance inverseDenominator →
  spatialExponent spatialRate distance propagationSpeed
    (balancedTime inverseDenominator spatialRate distance)
  ≡ commonBalancedExponent
      curvature spatialRate distance inverseDenominator
    + spatialRate * distance
      * (1ℚ - inverseDenominator
          * decayDenominator curvature spatialRate propagationSpeed)
balancedSpatialDecompositionExact
    curvature spatialRate propagationSpeed distance inverseDenominator =
  solve
    (curvature ∷ spatialRate ∷ propagationSpeed ∷
     distance ∷ inverseDenominator ∷ [])

balancedSpatialExponentExact :
  ∀ curvature spatialRate propagationSpeed distance inverseDenominator →
  inverseDenominator
    * decayDenominator curvature spatialRate propagationSpeed
  ≡ 1ℚ →
  spatialExponent spatialRate distance propagationSpeed
    (balancedTime inverseDenominator spatialRate distance)
  ≡ commonBalancedExponent
      curvature spatialRate distance inverseDenominator
balancedSpatialExponentExact
    curvature spatialRate propagationSpeed distance inverseDenominator inverseLaw =
  trans
    (balancedSpatialDecompositionExact
      curvature spatialRate propagationSpeed distance inverseDenominator)
    (trans
      (cong
        (λ selected →
          commonBalancedExponent
            curvature spatialRate distance inverseDenominator
          + spatialRate * distance * (1ℚ - selected))
        inverseLaw)
      (solve
        (curvature ∷ spatialRate ∷ propagationSpeed ∷
         distance ∷ inverseDenominator ∷ [])))

balancedExponentsAgree :
  ∀ curvature spatialRate propagationSpeed distance inverseDenominator →
  inverseDenominator
    * decayDenominator curvature spatialRate propagationSpeed
  ≡ 1ℚ →
  temporalExponent curvature
    (balancedTime inverseDenominator spatialRate distance)
  ≡ spatialExponent spatialRate distance propagationSpeed
      (balancedTime inverseDenominator spatialRate distance)
balancedExponentsAgree
    curvature spatialRate propagationSpeed distance inverseDenominator inverseLaw =
  trans
    (balancedTemporalExponentExact
      curvature spatialRate propagationSpeed distance inverseDenominator)
    (sym
      (balancedSpatialExponentExact
        curvature spatialRate propagationSpeed distance inverseDenominator
        inverseLaw))

configuredCurvature configuredSpatialRate configuredSpeed : ℚ
configuredCurvature = + 1 / 2
configuredSpatialRate = + 1 / 1
configuredSpeed = + 1 / 1

configuredInverseDenominator : ℚ
configuredInverseDenominator = + 1 / 2

configuredInverseLaw :
  configuredInverseDenominator
    * decayDenominator
        configuredCurvature configuredSpatialRate configuredSpeed
  ≡ 1ℚ
configuredInverseLaw = solve []

configuredBalancedTimeExact :
  ∀ distance →
  balancedTime configuredInverseDenominator configuredSpatialRate distance
  ≡ (+ 1 / 2) * distance
configuredBalancedTimeExact distance = solve (distance ∷ [])

configuredCommonExponentExact :
  ∀ distance →
  temporalExponent configuredCurvature
    (balancedTime configuredInverseDenominator configuredSpatialRate distance)
  ≡ (+ 1 / 2) * distance
configuredCommonExponentExact distance = solve (distance ∷ [])
