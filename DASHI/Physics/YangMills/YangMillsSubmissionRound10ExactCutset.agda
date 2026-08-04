module DASHI.Physics.YangMills.YangMillsSubmissionRound10ExactCutset where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanBishopFactorialPowerRecurrenceExact as Recurrence
import DASHI.Physics.YangMills.BalabanBishopConcreteFactorialCoefficientDischargeExact as Factorial
import DASHI.Physics.YangMills.BalabanBishopSeriesParityAndLimitExact as BishopParity
import DASHI.Physics.YangMills.BalabanBishopConcreteSeriesConvergenceTransportExact as SeriesTransport
import DASHI.Physics.YangMills.BalabanBishopAlternatingBracketFromMonotoneLimitsExact as Brackets
import DASHI.Physics.YangMills.BalabanP06PhysicalModelLeafLightweightExact as P06Light
import DASHI.Physics.YangMills.BalabanP11PhysicalPrefixTailEntropyExact as P11
import DASHI.Physics.YangMills.BalabanStepVFiniteGeometricBackendExact as StepV
import DASHI.Physics.YangMills.BalabanStepVBishopFiniteGeometricExact as BishopGeometric
import DASHI.Physics.YangMills.BalabanP10P33PhysicalCutsetExact as P10P33
import DASHI.Physics.YangMills.BalabanGate4ParityIntegrationExact as Gate4
import DASHI.Physics.YangMills.YangMillsRGParitySISpineExact as Endpoint
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Round ten removes four formerly independent leaves:
--
-- * reciprocal-factorial coefficient comparison;
-- * transformed sine/cosine convergence once term parity is known;
-- * order closure once alternating subsequence interlacing is known;
-- * ordinary finite geometric summation once 0 <= q < 1 is known.
--
-- The remaining fields below are therefore the exact post-round-ten physical
-- frontier rather than a repetition of already owned reducers.
------------------------------------------------------------------------

round10FactorialCoefficientSteps :
  Recurrence.ConcreteFactorialCoefficientStepBounds
round10FactorialCoefficientSteps =
  Factorial.concreteFactorialCoefficientStepBounds

record Round10BishopPhysicalCutset : Set₁ where
  field
    elementarySeries : Elementary.BishopElementaryPowerSeriesData

    sineTermsOdd :
      BishopParity.BishopOddTermFamily
        (Elementary.sineTerm elementarySeries)

    cosineTermsEven :
      BishopParity.BishopEvenTermFamily
        (Elementary.cosineTerm elementarySeries)

    sineCosineInterlacing :
      Brackets.BishopSineCosineInterlacingData

    interlacingUsesTheElementarySeries : Set
    interlacingUsesTheElementarySeriesEvidence :
      interlacingUsesTheElementarySeries

open Round10BishopPhysicalCutset public

round10ParityInputs :
  (inputs : Round10BishopPhysicalCutset) →
  BishopParity.BishopSeriesLimitParityInputs
    (elementarySeries inputs)
round10ParityInputs inputs =
  SeriesTransport.bishopSeriesLimitParityInputsFromTermParity
    (sineTermsOdd inputs)
    (cosineTermsEven inputs)

round10AlternatingBrackets :
  Round10BishopPhysicalCutset →
  BishopParity.ConcreteBishopAlternatingBrackets
round10AlternatingBrackets inputs =
  Brackets.concreteBishopAlternatingBracketsFromInterlacing
    (sineCosineInterlacing inputs)

record Round10LocalPhysicalCutset : Set₁ where
  field
    bishop : Round10BishopPhysicalCutset

    p06LightweightLeaf :
      P06Light.P06LightweightPhysicalModelLeaf

    lightweightP06AgreesWithLegacyConsumers : Set
    lightweightP06AgreesWithLegacyConsumersEvidence :
      lightweightP06AgreesWithLegacyConsumers

    remainingLegacyCountNeighboursConsumersMigrated : Set
    remainingLegacyCountNeighboursConsumersMigratedEvidence :
      remainingLegacyCountNeighboursConsumersMigrated

    p11PhysicalPrefixTail : P11.P11PhysicalPrefixTailInputs

    p10PhysicalSuppression : P10P33.P10LargeFieldPhysicalChain
    p33PhysicalEllipticity : P10P33.P33LinkEllipticityPhysicalChain

    gate4Parity : Gate4.Gate4ParityPackage

open Round10LocalPhysicalCutset public

record Round10StepVCutset : Set₁ where
  field
    geometricRatio : BishopGeometric.BishopGeometricRatio

    polynomialDegree : Nat
    polynomialWeightedBound :
      StepV.PolynomiallyWeightedGeometricBound
        BishopGeometric.bishopOrderedSemiringKernel
        (BishopGeometric.ratio geometricRatio)
        polynomialDegree

    positiveLogarithmExponentialBackend : Set
    positiveLogarithmExponentialBackendEvidence :
      positiveLogarithmExponentialBackend

    physicalOscillationShells : Set
    physicalOscillationShellsEvidence : physicalOscillationShells

    shellDecompositionMatchesActualKPNeighbourhood : Set
    shellDecompositionMatchesActualKPNeighbourhoodEvidence :
      shellDecompositionMatchesActualKPNeighbourhood

    weightedActivityDecayUsesP10AndP33 : Set
    weightedActivityDecayUsesP10AndP33Evidence :
      weightedActivityDecayUsesP10AndP33

open Round10StepVCutset public

round10FiniteGeometricBound :
  (inputs : Round10StepVCutset) →
  StepV.FiniteGeometricUniformBound
    BishopGeometric.bishopOrderedSemiringKernel
    (BishopGeometric.ratio (geometricRatio inputs))
round10FiniteGeometricBound inputs =
  BishopGeometric.bishopFiniteGeometricUniformBound
    (geometricRatio inputs)

record Round10GlobalEndpointCutset : Set₁ where
  field
    Scalar : Set
    parityAndSI : Endpoint.YangMillsParitySISpine Scalar

    dlrSmallnessFromStepV : Set
    dlrSmallnessFromStepVEvidence : dlrSmallnessFromStepV

    crossScaleInfluenceSummability : Set
    crossScaleInfluenceSummabilityEvidence :
      crossScaleInfluenceSummability

    uniformLogSobolevInequality : Set
    uniformLogSobolevInequalityEvidence :
      uniformLogSobolevInequality

    fixedLatticeSpectralGap : Set
    fixedLatticeSpectralGapEvidence : fixedLatticeSpectralGap

    thermodynamicLimitExistsAndIsUnique : Set
    thermodynamicLimitExistsAndIsUniqueEvidence :
      thermodynamicLimitExistsAndIsUnique

    cutoffRemovalExistsAndIsSchemeIndependent : Set
    cutoffRemovalExistsAndIsSchemeIndependentEvidence :
      cutoffRemovalExistsAndIsSchemeIndependent

    osReconstructionHypothesesVerified : Set
    osReconstructionHypothesesVerifiedEvidence :
      osReconstructionHypothesesVerified

    positivePhysicalSIMassGap : Set
    positivePhysicalSIMassGapEvidence :
      positivePhysicalSIMassGap

open Round10GlobalEndpointCutset public

record Round10CompleteCutset : Set₁ where
  field
    local : Round10LocalPhysicalCutset
    stepV : Round10StepVCutset
    global : Round10GlobalEndpointCutset

    localStepVTypesAgree : Set
    localStepVTypesAgreeEvidence : localStepVTypesAgree

    stepVGlobalTypesAgree : Set
    stepVGlobalTypesAgreeEvidence : stepVGlobalTypesAgree

    theoremBoundary : String

open Round10CompleteCutset public

round10ExactCutsetDefinitionLevel : ProofLevel
round10ExactCutsetDefinitionLevel = machineChecked

round10BishopCoefficientAndTransportLevel : ProofLevel
round10BishopCoefficientAndTransportLevel = machineChecked

round10OrdinaryFiniteGeometricBoundLevel : ProofLevel
round10OrdinaryFiniteGeometricBoundLevel = machineChecked

round10ConcreteInterlacingInputsLevel : ProofLevel
round10ConcreteInterlacingInputsLevel = conditional

round10P06P11P10P33PhysicalInputsLevel : ProofLevel
round10P06P11P10P33PhysicalInputsLevel = conditional

round10PolynomialShellAndGlobalEndpointLevel : ProofLevel
round10PolynomialShellAndGlobalEndpointLevel = conditional
