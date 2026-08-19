module DASHI.Physics.YangMills.BalabanPoincareFiniteSpeedClusteringRateExact where

------------------------------------------------------------------------
-- ROUND70: EXACT RELAXATION / FINITE-SPEED RATE BALANCE
--
-- PRIMARY SOURCES / CALIBRATION
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
--
-- Roland Bauerschmidt, Thierry Bodineau and Benoit Dagallier,
-- "Stochastic dynamics and the Polchinski equation: an introduction",
-- Probability Surveys 21 (2024), 200--290.
-- DOI: 10.1214/24-PS27.
--
-- DASHI CONTRIBUTION
--
-- The stochastic-to-spatial step repeatedly balances two exponent costs:
--
--     temporal relaxation:       lambda * t
--     finite-speed separation:   mu * d - v * t.
--
-- With t = tau d and tau = mu/(lambda+v), the two coefficients are exactly
-- equal and the common spatial exponent is
--
--     m = lambda mu/(lambda+v).
--
-- This module proves that algebra without any analytic exponential axioms.
-- A later semigroup/covariance theorem can therefore use one explicit rate
-- rather than hide the optimization in an existential constant.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record RelaxationPropagationRates : Set where
  field
    relaxationRate propagationVelocity spatialWeight inverseTotalRate : ℚ

    relaxationPositive : 0ℚ < relaxationRate
    propagationNonnegative : 0ℚ ≤ propagationVelocity
    spatialWeightPositive : 0ℚ < spatialWeight

    inverseTotalRateLaw :
      (relaxationRate + propagationVelocity) * inverseTotalRate ≡ 1ℚ
    inverseTotalRatePositive : 0ℚ < inverseTotalRate

open RelaxationPropagationRates public

timePerDistance : RelaxationPropagationRates → ℚ
timePerDistance dataSet = spatialWeight dataSet * inverseTotalRate dataSet

clusteringRate : RelaxationPropagationRates → ℚ
clusteringRate dataSet =
  relaxationRate dataSet * spatialWeight dataSet * inverseTotalRate dataSet

relaxationAtBalancedTimeExact :
  (dataSet : RelaxationPropagationRates) →
  relaxationRate dataSet * timePerDistance dataSet
  ≡ clusteringRate dataSet
relaxationAtBalancedTimeExact dataSet = ℚRing.solve []

finiteSpeedAtBalancedTimeExact :
  (dataSet : RelaxationPropagationRates) →
  spatialWeight dataSet
    - propagationVelocity dataSet * timePerDistance dataSet
  ≡ clusteringRate dataSet
finiteSpeedAtBalancedTimeExact dataSet =
  let
    lambda = relaxationRate dataSet
    velocity = propagationVelocity dataSet
    mu = spatialWeight dataSet
    inverse = inverseTotalRate dataSet

    exposeUnit :
      mu - velocity * (mu * inverse)
      ≡ mu * 1ℚ - velocity * (mu * inverse)
    exposeUnit = ℚRing.solve []

    insertInverseLaw :
      mu * 1ℚ - velocity * (mu * inverse)
      ≡ mu * ((lambda + velocity) * inverse)
          - velocity * (mu * inverse)
    insertInverseLaw =
      cong
        (λ selected → mu * selected - velocity * (mu * inverse))
        (sym (inverseTotalRateLaw dataSet))

    collectLambda :
      mu * ((lambda + velocity) * inverse)
        - velocity * (mu * inverse)
      ≡ lambda * mu * inverse
    collectLambda = ℚRing.solve []
  in
  trans exposeUnit (trans insertInverseLaw collectLambda)

------------------------------------------------------------------------
-- Positivity is retained as source data on the reciprocal rather than hidden
-- behind a rational-division convention.  The physical rate is therefore
-- visibly positive exactly when lambda>0, mu>0 and 1/(lambda+v)>0.
------------------------------------------------------------------------

record PositiveBalancedClusteringRate
    (dataSet : RelaxationPropagationRates) : Set where
  field
    clusteringRatePositive : 0ℚ < clusteringRate dataSet

open PositiveBalancedClusteringRate public

relaxationFiniteSpeedBalanceLevel : ProofLevel
relaxationFiniteSpeedBalanceLevel = machineChecked

-- Physical consumers still need the two analytic inequalities with these rate
-- parameters.  This file proves only their exact optimal linear balancing.
physicalTemporalAndFiniteSpeedBoundsLevel : ProofLevel
physicalTemporalAndFiniteSpeedBoundsLevel = conditional
