module DASHI.Biology.IIT4FiniteProbabilityRepertoireExact where

open import DASHI.Core.Prelude

import DASHI.Biology.IIT4FiniteCausalStructureExact as IIT4

------------------------------------------------------------------------
-- EXACT FINITE PROBABILITY INPUTS FOR IIT 4.0
--
-- IIT 4.0 starts from interventional conditional probabilities derived from a
-- transition probability function.  This owner computes the finite rational
-- inputs exactly as numerator/denominator pairs from the repository's finite
-- transition-weight carrier.  Fractions are intentionally not quotient-reduced:
-- equality of represented rationals and logarithmic evaluation belong to the
-- downstream scalar backend, while the finite counting source remains exact.
------------------------------------------------------------------------

record ProbabilityFraction : Set where
  constructor probabilityFraction
  field
    numerator : Nat
    denominator : Nat

open ProbabilityFraction public

sumTargetWeights :
  (system : IIT4.FiniteCausalSystem) →
  IIT4.StateOf system →
  List (IIT4.StateOf system) →
  Nat
sumTargetWeights system source [] = 0
sumTargetWeights system source (target ∷ rest) =
  IIT4.transitionWeight system source target
  + sumTargetWeights system source rest

rowWeightTotal :
  (system : IIT4.FiniteCausalSystem) →
  IIT4.StateOf system → Nat
rowWeightTotal system source =
  sumTargetWeights system source
    (IIT4.enumeration (IIT4.states system))

sumIncomingWeights :
  (system : IIT4.FiniteCausalSystem) →
  IIT4.StateOf system →
  List (IIT4.StateOf system) →
  Nat
sumIncomingWeights system target [] = 0
sumIncomingWeights system target (source ∷ rest) =
  IIT4.transitionWeight system source target
  + sumIncomingWeights system target rest

incomingWeightTotal :
  (system : IIT4.FiniteCausalSystem) →
  IIT4.StateOf system → Nat
incomingWeightTotal system target =
  sumIncomingWeights system target
    (IIT4.enumeration (IIT4.states system))

sumAllRows :
  (system : IIT4.FiniteCausalSystem) →
  List (IIT4.StateOf system) → Nat
sumAllRows system [] = 0
sumAllRows system (source ∷ rest) =
  rowWeightTotal system source + sumAllRows system rest

totalTransitionWeight :
  (system : IIT4.FiniteCausalSystem) → Nat
totalTransitionWeight system =
  sumAllRows system (IIT4.enumeration (IIT4.states system))

-- Exact effect-side interventional conditional probability p_e(target | source)
-- when the transition weights use the declared row normalisation.
effectConditionalFraction :
  (system : IIT4.FiniteCausalSystem) →
  IIT4.StateOf system → IIT4.StateOf system →
  ProbabilityFraction
effectConditionalFraction system source target =
  probabilityFraction
    (IIT4.transitionWeight system source target)
    (rowWeightTotal system source)

-- Uniform-source finite marginal induced by the transition table.  For a
-- row-normalized deterministic n-state TPM this is incoming-count / n.
unconstrainedEffectFraction :
  (system : IIT4.FiniteCausalSystem) →
  IIT4.StateOf system → ProbabilityFraction
unconstrainedEffectFraction system target =
  probabilityFraction
    (incomingWeightTotal system target)
    (totalTransitionWeight system)

record FiniteEffectRepertoire
    (system : IIT4.FiniteCausalSystem)
    (source : IIT4.StateOf system) : Set₁ where
  constructor finiteEffectRepertoire
  field
    probabilityAt : IIT4.StateOf system → ProbabilityFraction
    exactFromTransitionTable :
      (target : IIT4.StateOf system) →
      probabilityAt target ≡ effectConditionalFraction system source target

open FiniteEffectRepertoire public

canonicalFiniteEffectRepertoire :
  (system : IIT4.FiniteCausalSystem) →
  (source : IIT4.StateOf system) →
  FiniteEffectRepertoire system source
canonicalFiniteEffectRepertoire system source =
  finiteEffectRepertoire
    (effectConditionalFraction system source)
    (λ target → refl)

------------------------------------------------------------------------
-- Cause-side carrier.
--
-- Backward/interventional cause probabilities are not identified with the
-- forward table by definition.  They are supplied with an exact finite receipt
-- because IIT's cause repertoire requires its own intervention semantics.
------------------------------------------------------------------------

record FiniteCauseRepertoire
    (system : IIT4.FiniteCausalSystem)
    (current : IIT4.StateOf system) : Set₁ where
  constructor finiteCauseRepertoire
  field
    causeProbabilityAt : IIT4.StateOf system → ProbabilityFraction
    causeNormalisationReceipt : String
    interventionalBackwardReceipt : String

open FiniteCauseRepertoire public

------------------------------------------------------------------------
-- Partitioned repertoires are separate objects.  Cutting a system changes the
-- relevant probabilities; no graph cut count is allowed to stand in for them.
------------------------------------------------------------------------

record PartitionedProbability
    (system : IIT4.FiniteCausalSystem) : Set where
  constructor partitionedProbability
  field
    partition : IIT4.SystemPartition system
    source target : IIT4.StateOf system
    unpartitioned : ProbabilityFraction
    partitioned : ProbabilityFraction
    cutConstructionReceipt : String

open PartitionedProbability public

record FiniteProbabilityBoundary : Set where
  constructor finiteProbabilityBoundary
  field
    transitionCountsProduceExactFractionInputs : Bool
    causeAndEffectRepertoiresAreDefinitionallyIdentical : Bool
    partitionedProbabilityEqualsGraphCutCount : Bool
    rationalInputAlreadyImplementsLogarithm : Bool
    zeroDenominatorSilentlyAcceptedAsProbability : Bool
    scalarEvaluationRequiresSeparateBackend : Bool

open FiniteProbabilityBoundary public

canonicalFiniteProbabilityBoundary : FiniteProbabilityBoundary
canonicalFiniteProbabilityBoundary =
  finiteProbabilityBoundary
    true false false false false true

forwardTableDoesNotManufactureCauseRepertoire :
  causeAndEffectRepertoiresAreDefinitionallyIdentical
    canonicalFiniteProbabilityBoundary ≡ false
forwardTableDoesNotManufactureCauseRepertoire = refl

finiteFractionsDoNotManufactureLogs :
  rationalInputAlreadyImplementsLogarithm
    canonicalFiniteProbabilityBoundary ≡ false
finiteFractionsDoNotManufactureLogs = refl
