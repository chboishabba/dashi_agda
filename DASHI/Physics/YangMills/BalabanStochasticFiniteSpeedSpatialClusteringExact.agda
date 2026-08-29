module DASHI.Physics.YangMills.BalabanStochasticFiniteSpeedSpatialClusteringExact where

------------------------------------------------------------------------
-- ROUND70: STOCHASTIC RELAXATION + LOCAL PROPAGATION -> SPATIAL CLUSTERING
--
-- PRIMARY SOURCES / CALIBRATION
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
--
-- Ali Naddaf and Thomas Spencer,
-- "On Homogenization and Scaling Limit of Some Gradient Perturbations of a
-- Massless Free Field", Communications in Mathematical Physics 183 (1997),
-- 55--84. DOI: 10.1007/s002200050020.
--
-- Roland Bauerschmidt, Thierry Bodineau and Benoit Dagallier,
-- "Stochastic dynamics and the Polchinski equation: an introduction",
-- Probability Surveys 21 (2024), 200--290.
-- DOI: 10.1214/24-PS27.
--
-- SOURCE / AUTHORITY BOUNDARY
--
-- A Poincare or log-Sobolev inequality is a relaxation statement for the
-- auxiliary stochastic dynamics.  It is NOT definitionally the physical
-- Yang--Mills Hamiltonian gap.  To reach the Clay spectral endpoint one first
-- needs spatial/Euclidean clustering on the same gauge-invariant measure and
-- then the existing Osterwalder--Schrader spectral interpretation.
--
-- DASHI CONTRIBUTION
--
-- Make the time optimization and covariance split explicit.  For every pair of
-- local observables at distance d, evaluate the stochastic covariance identity
-- at
--
--     t_d = [mu/(lambda+v)] d.
--
-- The exact rate algebra is owned by
-- BalabanPoincareFiniteSpeedClusteringRateExact.  Once the two analytic pieces
-- are bounded at this selected time, their sum gives the declared spatial
-- envelope.  No stochastic spectral-gap witness is promoted directly to the
-- OS Hamiltonian.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _*_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanPoincareFiniteSpeedClusteringRateExact as Rate

record StochasticFiniteSpeedClusteringData
    (Observable Bound : Set) : Set₁ where
  field
    rates : Rate.RelaxationPropagationRates

    distance : Observable → Observable → Nat
    covariance : Observable → Observable → Bound

    temporalTerm : ℚ → Observable → Observable → Bound
    propagationTerm : ℚ → Observable → Observable → Bound
    spatialEnvelope : Observable → Observable → Bound

    add : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (add left right) (add leftUpper rightUpper)

    -- Semigroup/covariance representation split at arbitrary stochastic time.
    covarianceSplitAtTime : ∀ time left right →
      LessEqual
        (covariance left right)
        (add
          (temporalTerm time left right)
          (propagationTerm time left right))

    temporalBalancedEnvelope propagationBalancedEnvelope :
      Observable → Observable → Bound

    -- These are the two genuine analytic estimates.  The time itself is NOT a
    -- supplied witness: DASHI fixes it from the exact rate balance.
    temporalRelaxationAtBalancedTime : ∀ left right →
      LessEqual
        (temporalTerm
          (Rate.timePerDistance rates
            * Sums.natAsRational (distance left right))
          left right)
        (temporalBalancedEnvelope left right)

    finiteSpeedAtBalancedTime : ∀ left right →
      LessEqual
        (propagationTerm
          (Rate.timePerDistance rates
            * Sums.natAsRational (distance left right))
          left right)
        (propagationBalancedEnvelope left right)

    balancedPiecesGiveSpatialEnvelope : ∀ left right →
      LessEqual
        (add
          (temporalBalancedEnvelope left right)
          (propagationBalancedEnvelope left right))
        (spatialEnvelope left right)

open StochasticFiniteSpeedClusteringData public

balancedStochasticTime :
  ∀ {Observable Bound} →
  StochasticFiniteSpeedClusteringData Observable Bound →
  Observable → Observable → ℚ
balancedStochasticTime dataSet left right =
  Rate.timePerDistance (rates dataSet)
    * Sums.natAsRational (distance dataSet left right)

spatialClusteringFromRelaxationAndFiniteSpeed :
  ∀ {Observable Bound}
    (dataSet : StochasticFiniteSpeedClusteringData Observable Bound) →
  ∀ left right →
  LessEqual dataSet
    (covariance dataSet left right)
    (spatialEnvelope dataSet left right)
spatialClusteringFromRelaxationAndFiniteSpeed dataSet left right =
  let
    time = balancedStochasticTime dataSet left right
    split = covarianceSplitAtTime dataSet time left right
    balanced = addMonotone dataSet
      (temporalRelaxationAtBalancedTime dataSet left right)
      (finiteSpeedAtBalancedTime dataSet left right)
  in
  transitive dataSet split
    (transitive dataSet balanced
      (balancedPiecesGiveSpatialEnvelope dataSet left right))

stochasticFiniteSpeedSpatialClusteringCompilerLevel : ProofLevel
stochasticFiniteSpeedSpatialClusteringCompilerLevel = machineChecked

-- Remaining physical content is sharply localized:
--
-- * temporalRelaxationAtBalancedTime comes from the SAME-measure
--   Polchinski/LSI/Poincare estimate;
-- * finiteSpeedAtBalancedTime comes from the SAME local derivative generator,
--   the exact below-distance Dyson cancellation, and its analytic high-order
--   tail/row-mass estimate;
-- * spatialEnvelope must be an actual exponential physical-distance envelope
--   whose rate is the exact m=lambda*mu/(lambda+v) from Rate.
physicalYMStochasticFiniteSpeedClusteringLevel : ProofLevel
physicalYMStochasticFiniteSpeedClusteringLevel = conditional
