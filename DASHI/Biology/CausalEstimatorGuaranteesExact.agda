module DASHI.Biology.CausalEstimatorGuaranteesExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)

import DASHI.Biology.CausalEffectEstimandExact as Estimand
import DASHI.Biology.CausalEstimandStatisticalRealisationExact as Statistical
import DASHI.Biology.FiniteRationalCausalEstimandExpectationExact as FiniteTarget
import DASHI.Cognition.PNF.GenericExpectedFibreRateExact as Expected

------------------------------------------------------------------------
-- ESTIMATOR GUARANTEES
--
-- Estimand, estimator, realized estimate, and uncertainty are already distinct.
-- This owner adds proof-bearing guarantee coordinates.  Bias/unbiasedness,
-- consistency, dispersion, coverage, and power remain separate claims; no one
-- is inferred from another, and asymptotic semantics are application-supplied.
------------------------------------------------------------------------

record BiasGuarantee
    {estimand : Estimand.CausalEffectEstimand}
    (procedure : Statistical.EstimatorProcedure estimand) : Set₁ where
  constructor bias-guarantee
  field
    BiasProperty : Set
    biasReceipt : BiasProperty
    biasReference : String

open BiasGuarantee public

record ConsistencyGuarantee
    {estimand : Estimand.CausalEffectEstimand}
    (procedure : Statistical.EstimatorProcedure estimand) : Set₁ where
  constructor consistency-guarantee
  field
    Index : Set
    ConsistencyProperty : Index → Set
    consistencyReceipt : (index : Index) → ConsistencyProperty index
    limitOrRefinementReference : String
    consistencyReference : String

open ConsistencyGuarantee public

record DispersionGuarantee
    {estimand : Estimand.CausalEffectEstimand}
    (procedure : Statistical.EstimatorProcedure estimand) : Set₁ where
  constructor dispersion-guarantee
  field
    Dispersion : Set
    dispersionOf : Statistical.Sample procedure → Dispersion
    DispersionProperty : Statistical.Sample procedure → Dispersion → Set
    dispersionReceipt :
      (sample : Statistical.Sample procedure) →
      DispersionProperty sample (dispersionOf sample)
    dispersionReference : String

open DispersionGuarantee public

record CoverageGuarantee
    {estimand : Estimand.CausalEffectEstimand}
    {procedure : Statistical.EstimatorProcedure estimand}
    (intervalProcedure : Statistical.ConfidenceIntervalEstimatorRealisation procedure) : Set₁ where
  constructor coverage-guarantee
  field
    coverageIsSameProcedure :
      (sample : Statistical.Sample procedure) →
      Statistical.CoverageProperty intervalProcedure sample
    repeatedSamplingReference : String
    coverageGuaranteeReference : String

open CoverageGuarantee public

record PowerGuarantee
    {estimand : Estimand.CausalEffectEstimand}
    (procedure : Statistical.EstimatorProcedure estimand) : Set₁ where
  constructor power-guarantee
  field
    Alternative : Set
    PowerProperty : Alternative → Set
    powerReceipt : (alternative : Alternative) → PowerProperty alternative
    decisionRuleReference : String
    alternativeReference : String
    powerReference : String

open PowerGuarantee public

------------------------------------------------------------------------
-- Finite rational sampling specialization.
--
-- This is an exact finite law over realized samples.  It reuses the repo's
-- normalized rational probability atom, but it is not a general probability
-- measure or an asymptotic sampling theorem.
------------------------------------------------------------------------

record WeightedEstimatorSample
    {estimand : Estimand.CausalEffectEstimand}
    (procedure : Statistical.EstimatorProcedure estimand) : Set where
  constructor weighted-estimator-sample
  field
    probability : Expected.ProbabilityAtom
    sample : Statistical.Sample procedure
    sampleReference : String

open WeightedEstimatorSample public

sampleMass :
  ∀ {estimand procedure} →
  WeightedEstimatorSample {estimand} procedure → ℚ
sampleMass atom = Expected.probabilityMass (probability atom)

finiteSamplingMass :
  ∀ {estimand procedure} →
  List (WeightedEstimatorSample {estimand} procedure) → ℚ
finiteSamplingMass [] = 0ℚ
finiteSamplingMass (atom ∷ atoms) =
  sampleMass atom + finiteSamplingMass atoms

record NormalizedFiniteEstimatorSamplingLaw
    {estimand : Estimand.CausalEffectEstimand}
    (procedure : Statistical.EstimatorProcedure estimand) : Set₁ where
  constructor normalized-finite-estimator-sampling-law
  field
    atoms : List (WeightedEstimatorSample procedure)
    normalized : finiteSamplingMass atoms ≡ 1ℚ
    samplingLawReference : String
    weightingReference : String

open NormalizedFiniteEstimatorSamplingLaw public

finiteExpectedEstimatorOutput :
  ∀ {estimand}
    {procedure : Statistical.EstimatorProcedure estimand} →
  (estimateToRational : Statistical.Estimate procedure → ℚ) →
  List (WeightedEstimatorSample procedure) → ℚ
finiteExpectedEstimatorOutput {procedure = procedure} estimateToRational [] = 0ℚ
finiteExpectedEstimatorOutput {procedure = procedure} estimateToRational (atom ∷ atoms) =
  sampleMass atom
    * estimateToRational
        (Statistical.estimator procedure (sample atom))
  + finiteExpectedEstimatorOutput estimateToRational atoms

------------------------------------------------------------------------
-- Exact finite unbiasedness for an ATE-shaped finite target.
--
-- The estimator expectation is compared to the already-realized finite ATE;
-- the target is not reconstructed independently here.
------------------------------------------------------------------------

record FiniteRationalUnbiasedness
    {scope : Estimand.CausalEstimandScope}
    {algebra : Estimand.EffectAlgebra scope}
    {ate : Estimand.AveragePopulationEffectEstimand scope algebra}
    {targetRealisation : FiniteTarget.FiniteRationalEffectAlgebraRealisation scope algebra}
    (target : FiniteTarget.FiniteRationalAveragePopulationEffect ate targetRealisation)
    {genericEstimand : Estimand.CausalEffectEstimand}
    (procedure : Statistical.EstimatorProcedure genericEstimand) : Set₁ where
  constructor finite-rational-unbiasedness
  field
    law : NormalizedFiniteEstimatorSamplingLaw procedure
    estimateToRational : Statistical.Estimate procedure → ℚ

    expectedEstimatorEqualsTarget :
      finiteExpectedEstimatorOutput estimateToRational (atoms law)
      ≡ FiniteTarget.realisedAggregate target

    estimatorTargetReference : String
    unbiasednessReference : String

open FiniteRationalUnbiasedness public

finiteUnbiasedExpectationEqualsFiniteATE :
  ∀ {scope algebra ate targetRealisation target genericEstimand procedure} →
  (U : FiniteRationalUnbiasedness
    {scope} {algebra} {ate} {targetRealisation}
    target {genericEstimand} procedure) →
  finiteExpectedEstimatorOutput
    (estimateToRational U)
    (atoms (law U))
  ≡ FiniteTarget.finiteExpectedEffect
      (FiniteTarget.atoms (FiniteTarget.law targetRealisation))
finiteUnbiasedExpectationEqualsFiniteATE
  {target = target}
  {targetRealisation = targetRealisation}
  U =
  trans
    (expectedEstimatorEqualsTarget U)
    (FiniteTarget.realisedATEIsFiniteExpectation target)

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data UnbiasedMeansConsistentPermission : Set where

data ConsistentMeansUnbiasedPermission : Set where

data LowDispersionMeansUnbiasedPermission : Set where

data CoverageMeansCausalIdentificationPermission : Set where

data PowerMeansEffectTruthPermission : Set where

data FiniteUnbiasednessMeansAsymptoticConsistencyPermission : Set where

data NormalizedSamplingLawMeansRepresentativePopulationPermission : Set where

data ExpectedEstimatorEqualsOneTargetMeansUniversalTransportPermission : Set where

unbiasedDoesNotAutomaticallyMeanConsistent :
  UnbiasedMeansConsistentPermission → ⊥
unbiasedDoesNotAutomaticallyMeanConsistent ()

consistentDoesNotAutomaticallyMeanUnbiased :
  ConsistentMeansUnbiasedPermission → ⊥
consistentDoesNotAutomaticallyMeanUnbiased ()

lowDispersionDoesNotAutomaticallyMeanUnbiased :
  LowDispersionMeansUnbiasedPermission → ⊥
lowDispersionDoesNotAutomaticallyMeanUnbiased ()

coverageDoesNotIdentifyCause :
  CoverageMeansCausalIdentificationPermission → ⊥
coverageDoesNotIdentifyCause ()

powerDoesNotProveEffectTruth :
  PowerMeansEffectTruthPermission → ⊥
powerDoesNotProveEffectTruth ()

finiteUnbiasednessDoesNotCreateAsymptoticConsistency :
  FiniteUnbiasednessMeansAsymptoticConsistencyPermission → ⊥
finiteUnbiasednessDoesNotCreateAsymptoticConsistency ()

normalizedSamplingLawDoesNotProveRepresentativePopulation :
  NormalizedSamplingLawMeansRepresentativePopulationPermission → ⊥
normalizedSamplingLawDoesNotProveRepresentativePopulation ()

oneTargetExpectationDoesNotUniversallyTransport :
  ExpectedEstimatorEqualsOneTargetMeansUniversalTransportPermission → ⊥
oneTargetExpectationDoesNotUniversallyTransport ()

record CausalEstimatorGuaranteeBoundary : Set where
  constructor causal-estimator-guarantee-boundary
  field
    biasConsistencyDispersionCoveragePowerRemainDistinct : Bool
    finiteEstimatorExpectationIsExplicit : Bool
    finiteUnbiasednessCanBeProvedAgainstFiniteTarget : Bool
    unbiasednessAutomaticallyImpliesConsistency : Bool
    coverageAutomaticallyIdentifiesCause : Bool
    powerAutomaticallyProvesEffectTruth : Bool
    normalizedSamplingLawProvesRepresentativeness : Bool
    asymptoticProbabilityTheoryInventedHere : Bool

canonicalCausalEstimatorGuaranteeBoundary : CausalEstimatorGuaranteeBoundary
canonicalCausalEstimatorGuaranteeBoundary =
  causal-estimator-guarantee-boundary
    true true true false false false false false
