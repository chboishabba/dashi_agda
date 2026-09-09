module DASHI.Biology.FiniteRationalCausalEstimandExpectationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)

import DASHI.Biology.CausalEffectEstimandExact as Estimand
import DASHI.Cognition.PNF.GenericExpectedFibreRateExact as Expected

------------------------------------------------------------------------
-- FINITE RATIONAL REALISATION OF A CAUSAL EFFECT AGGREGATE
--
-- GenericExpectedFibreRateExact already owns a normalized finite rational
-- probability carrier.  This owner reuses that finite shape for causal-effect
-- aggregation.  It is intentionally not a general measure/probability space,
-- not an asymptotic theorem, and not an automatic realization of every causal
-- estimand.
------------------------------------------------------------------------

record WeightedCausalEffectAtom : Set where
  constructor weighted-causal-effect-atom
  field
    probability : Expected.ProbabilityAtom
    effect : ℚ
    atomReference : String

open WeightedCausalEffectAtom public

weightedMass : WeightedCausalEffectAtom → ℚ
weightedMass atom = Expected.probabilityMass (probability atom)

weightedContribution : WeightedCausalEffectAtom → ℚ
weightedContribution atom = weightedMass atom * effect atom

finiteProbabilityMass : List WeightedCausalEffectAtom → ℚ
finiteProbabilityMass [] = 0ℚ
finiteProbabilityMass (atom ∷ atoms) =
  weightedMass atom + finiteProbabilityMass atoms

finiteExpectedEffect : List WeightedCausalEffectAtom → ℚ
finiteExpectedEffect [] = 0ℚ
finiteExpectedEffect (atom ∷ atoms) =
  weightedContribution atom + finiteExpectedEffect atoms

record NormalizedFiniteCausalEffectLaw : Set where
  constructor normalized-finite-causal-effect-law
  field
    atoms : List WeightedCausalEffectAtom
    normalized : finiteProbabilityMass atoms ≡ 1ℚ
    populationReference : String
    weightingReference : String
    effectScaleReference : String

open NormalizedFiniteCausalEffectLaw public

------------------------------------------------------------------------
-- Bind the finite law to one EffectAlgebra.
--
-- EffectValue and PopulationAggregate are not definitionally forced to ℚ.
-- Instead an application supplies explicit realization maps and a theorem that
-- the target aggregate maps to the same finite expected effect.
------------------------------------------------------------------------

record FiniteRationalEffectAlgebraRealisation
    (scope : Estimand.CausalEstimandScope)
    (algebra : Estimand.EffectAlgebra scope) : Set₁ where
  constructor finite-rational-effect-algebra-realisation
  field
    law : NormalizedFiniteCausalEffectLaw

    effectToRational : Estimand.EffectValue algebra → ℚ
    aggregateToRational : Estimand.PopulationAggregate algebra → ℚ

    targetAggregateMatchesFiniteExpectation :
      aggregateToRational
        (Estimand.aggregatePopulation algebra
          (Estimand.population scope)
          (Estimand.unitEffectAtHorizon scope algebra))
      ≡ finiteExpectedEffect (atoms law)

    unitWeightingReference : String
    aggregateRealisationReference : String

open FiniteRationalEffectAlgebraRealisation public

------------------------------------------------------------------------
-- Specialized ATE-shaped binding.
------------------------------------------------------------------------

record FiniteRationalAveragePopulationEffect
    {scope : Estimand.CausalEstimandScope}
    {algebra : Estimand.EffectAlgebra scope}
    (ate : Estimand.AveragePopulationEffectEstimand scope algebra)
    (realisation : FiniteRationalEffectAlgebraRealisation scope algebra) : Set₁ where
  constructor finite-rational-average-population-effect
  field
    realisedAggregate : ℚ
    realisedAggregateIsATE :
      realisedAggregate
      ≡ aggregateToRational realisation
          (Estimand.aggregate ate)

    realisedAggregateIsFiniteExpectation :
      realisedAggregate
      ≡ finiteExpectedEffect (atoms (law realisation))

    estimateTargetReference : String

open FiniteRationalAveragePopulationEffect public

------------------------------------------------------------------------
-- Bridge to the canonical finite probability atom shape.
------------------------------------------------------------------------

canonicalProbabilityAtomOf : WeightedCausalEffectAtom → Expected.ProbabilityAtom
canonicalProbabilityAtomOf = probability

atomMassNonnegative :
  (atom : WeightedCausalEffectAtom) →
  0ℚ ≤ weightedMass atom
atomMassNonnegative atom =
  Expected.probabilityNonnegative (probability atom)

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data FiniteLawMeansGeneralProbabilitySpacePermission : Set where

data FiniteExpectationMeansPopulationTruthPermission : Set where

data NormalizedWeightsMeansRepresentativeSamplingPermission : Set where

data WeightedAverageMeansCausalIdentificationPermission : Set where

data ATERealisationMeansATTPermission : Set where

data FiniteLawMeansAsymptoticGuaranteePermission : Set where

finiteLawDoesNotBecomeGeneralProbabilitySpace :
  FiniteLawMeansGeneralProbabilitySpacePermission → ⊥
finiteLawDoesNotBecomeGeneralProbabilitySpace ()

finiteExpectationDoesNotBecomePopulationTruth :
  FiniteExpectationMeansPopulationTruthPermission → ⊥
finiteExpectationDoesNotBecomePopulationTruth ()

normalizedWeightsDoNotProveRepresentativeSampling :
  NormalizedWeightsMeansRepresentativeSamplingPermission → ⊥
normalizedWeightsDoNotProveRepresentativeSampling ()

weightedAverageDoesNotIdentifyCause :
  WeightedAverageMeansCausalIdentificationPermission → ⊥
weightedAverageDoesNotIdentifyCause ()

ateRealisationDoesNotBecomeATT :
  ATERealisationMeansATTPermission → ⊥
ateRealisationDoesNotBecomeATT ()

finiteLawDoesNotCreateAsymptoticGuarantee :
  FiniteLawMeansAsymptoticGuaranteePermission → ⊥
finiteLawDoesNotCreateAsymptoticGuarantee ()

record FiniteRationalCausalEstimandExpectationBoundary : Set where
  constructor finite-rational-causal-estimand-expectation-boundary
  field
    finiteNormalizedProbabilityCarrierReused : Bool
    effectAndProbabilityMassRemainDistinct : Bool
    aggregateNeedsExplicitRationalRealisation : Bool
    normalizedWeightsProveRepresentativeSampling : Bool
    finiteExpectationProvesCausalIdentification : Bool
    finiteLawIsGeneralProbabilitySpace : Bool
    asymptoticGuaranteeInstalled : Bool

canonicalFiniteRationalCausalEstimandExpectationBoundary :
  FiniteRationalCausalEstimandExpectationBoundary
canonicalFiniteRationalCausalEstimandExpectationBoundary =
  finite-rational-causal-estimand-expectation-boundary
    true true true false false false false
