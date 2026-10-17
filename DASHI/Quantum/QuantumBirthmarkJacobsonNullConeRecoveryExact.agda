{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkJacobsonNullConeRecoveryExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- JACOBSON ALL-NULL-DIRECTIONS -> TENSOR MODULO METRIC COMPILER
--
-- Jacobson's local thermodynamic argument first produces a relation tested on
-- every null generator k.  Since g(k,k)=0, null contractions cannot determine
-- the pure-metric / cosmological term.  The exact algebraic task is therefore:
--
--   [defect(k,k)=0 for every null k]
--     + [null-cone rigidity theorem]
--   -> defect = Lambda * g.
--
-- This owner proves that compiler abstractly.  It does NOT manufacture the
-- Lorentzian null-cone rigidity theorem, the stress tensor, Unruh/Clausius, or
-- the continuum Raychaudhuri equation.
------------------------------------------------------------------------

record NullContractedFieldRelation : Set₁ where
  field
    Tensor : Set
    NullDirection : Set
    Scalar : Set

    zero : Scalar
    defect : Tensor
    nullContraction : Tensor → NullDirection → Scalar

    allNullDirections :
      (k : NullDirection) →
      nullContraction defect k ≡ zero

open NullContractedFieldRelation public

------------------------------------------------------------------------
-- Geometric rigidity payment.
--
-- A concrete Lorentzian implementation should prove that any symmetric
-- two-tensor whose quadratic contraction vanishes on every null direction is
-- proportional to the metric.  The metric multiple is intentionally abstract
-- here so this module does not assume coordinates, dimension, or a scalar
-- action that has not been paid by the selected spacetime carrier.
------------------------------------------------------------------------

record NullConeTensorRigidity
    (R : NullContractedFieldRelation) : Set₁ where
  field
    MetricCoefficient : Set
    metricMultiple : MetricCoefficient → Tensor R

    rigidity :
      (candidate : Tensor R) →
      ((k : NullDirection R) →
        nullContraction R candidate k ≡ zero R) →
      Σ MetricCoefficient (λ coefficient →
        candidate ≡ metricMultiple coefficient)

open NullConeTensorRigidity public

record TensorEquationModuloMetric
    (R : NullContractedFieldRelation)
    (G : NullConeTensorRigidity R) : Set where
  constructor tensorEquationModuloMetric
  field
    cosmologicalCoefficient : MetricCoefficient G
    tensorEquation :
      defect R ≡ metricMultiple G cosmologicalCoefficient

open TensorEquationModuloMetric public

recoverTensorEquationModuloMetric :
  (R : NullContractedFieldRelation) →
  (G : NullConeTensorRigidity R) →
  TensorEquationModuloMetric R G
recoverTensorEquationModuloMetric R G with
  rigidity G (defect R) (allNullDirections R)
... | coefficient , equation =
  tensorEquationModuloMetric coefficient equation

------------------------------------------------------------------------
-- Why the cosmological term is invisible at the preceding null-contracted
-- stage.  A concrete carrier can instantiate this with g_ab k^a k^b = 0.
------------------------------------------------------------------------

record MetricNullInvisibility
    (R : NullContractedFieldRelation)
    (G : NullConeTensorRigidity R) : Set₁ where
  field
    metricMultipleNull :
      (coefficient : MetricCoefficient G) →
      (k : NullDirection R) →
      nullContraction R (metricMultiple G coefficient) k ≡ zero R

open MetricNullInvisibility public

record NullConeRecoveryAuthorityBoundary : Set where
  constructor nullConeRecoveryAuthorityBoundary
  field
    tensorRecoveryCompilerOwned : Bool
    nullConeRigidityStillRequired : Bool
    stressEnergySameObjectStillRequired : Bool
    unruhClausiusStillRequired : Bool
    continuumRaychaudhuriStillRequired : Bool
    nullRelationAloneDoesNotFixCosmologicalTerm : Bool
    finiteFixtureDoesNotPayContinuumRigidity : Bool

canonicalNullConeRecoveryAuthorityBoundary :
  NullConeRecoveryAuthorityBoundary
canonicalNullConeRecoveryAuthorityBoundary =
  nullConeRecoveryAuthorityBoundary
    true true true true true true true

tensorRecoveryCompilerOwned : Bool
tensorRecoveryCompilerOwned = true

nullConeRigidityStillRequired : Bool
nullConeRigidityStillRequired = true

stressEnergySameObjectStillRequired : Bool
stressEnergySameObjectStillRequired = true

unruhClausiusStillRequired : Bool
unruhClausiusStillRequired = true

continuumRaychaudhuriStillRequired : Bool
continuumRaychaudhuriStillRequired = true

nullRelationAloneDoesNotFixCosmologicalTerm : Bool
nullRelationAloneDoesNotFixCosmologicalTerm = true
