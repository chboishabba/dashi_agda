module DASHI.ComputerScience.RSA260MixedActionNDimFibreInferenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260C3OrbitReducerHyperfabricExact as C3
import DASHI.ComputerScience.RSA260ReducerHyperfabricSourceDiligenceExact as Sources

------------------------------------------------------------------------
-- MIXED ACTION / NDIM FIBRE INFERENCE
--
-- Cross-pollination from the Fly structure-function lane:
-- retain structurally distinct fibres separately, prune/infer using structural
-- geometry only, freeze the candidate family, and only then ask the final
-- consumer/global operator whether the composition is admissible.
------------------------------------------------------------------------

record InternalCrossRepoSource : Set where
  constructor internal-cross-repo-source
  field
    repository : String
    branch : String
    path : String
    retainedLesson : String
    externalPrimarySource : Bool
open InternalCrossRepoSource public

flyNDimStructureFunctionSource : InternalCrossRepoSource
flyNDimStructureFunctionSource = internal-cross-repo-source
  "chboishabba/dashiBRAIN"
  "agent/malecns-real-benchmark-tranche"
  "dashi/analysis/ndim_structure_function.py"
  "keep directed/structural fibres separate; select structurally non-redundant fibres without outcome leakage; freeze before held-out/global evaluation"
  false

record RuntimeSource : Set where
  constructor runtime-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    gitBlob : String
    language : String
open RuntimeSource public

mixedActionSource : RuntimeSource
mixedActionSource = runtime-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_mixed_action_generator_inference_256_oracle.c"
  "15d9a4a751de950abc6a9c79a0b67c95d0d349ab"
  "322d15cc11cdf197b0296de40cb011d87b71a7ba"
  "C11"

multiFibreV4Source : RuntimeSource
multiFibreV4Source = runtime-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_multifibre_v4_action_inference_256_oracle.c"
  "55398e0f20be2ea876013230e21d59f955635789"
  "dc803b610781b9a9a5c09e6d3c9c22ac89de5c3d"
  "C11"

record MixedActionInferenceReceipt : Set where
  constructor mixed-action-inference-receipt
  field
    carrierCoordinates : Nat
    stableClasses : Nat
    inferredOrbitClasses : Nat
    refinementRounds : Nat
    inferredC2Classes : Nat
    inferredC3Classes : Nat
    inferredC4Classes : Nat
    residualCoordinates : Nat
    candidatePermutationCount : Nat
    orderTwoCandidates : Nat
    orderThreeCandidates : Nat
    orderFourCandidates : Nat
    generatorOrderComputedFromPermutation : Bool
    inducedOperatorGeometryUsedBeforeActionChoice : Bool
    finalQuotientPayoffUsedToChooseGenerator : Bool
    sourceEquivalentExecutionPassed : Bool
    exactGitBlobExecuted : Bool
    productionRSA260MatrixUsed : Bool
open MixedActionInferenceReceipt public

currentMixedActionInferenceReceipt : MixedActionInferenceReceipt
currentMixedActionInferenceReceipt = mixed-action-inference-receipt
  256 98 74 24
  20 24 30 24
  158 50 48 60
  true true false
  true false false

record MultiFibreV4Receipt : Set where
  constructor multifibre-v4-receipt
  field
    carrierCoordinates : Nat
    fourStateClasses : Nat
    requirementComponents : Nat
    classesPerRequirementComponent : Nat
    residualCoordinates : Nat
    primaryOperatorLocalPermutationCount : Nat
    structuralFibreCount : Nat
    intersectionPermutationCount : Nat
    intersectionNontrivialOrderTwoCount : Nat
    intersectionOrderFourCount : Nat
    primaryOperatorAloneDeterminesV4 : Bool
    fibreIntersectionDeterminesV4CandidateFamily : Bool
    oneLocalV4MoveCommutesGlobally : Bool
    requirementClosedV4GeneratorsCommuting : Nat
    sourceEquivalentExecutionPassed : Bool
    exactGitBlobExecuted : Bool
    productionRSA260MatrixUsed : Bool
open MultiFibreV4Receipt public

currentMultiFibreV4Receipt : MultiFibreV4Receipt
currentMultiFibreV4Receipt = multifibre-v4-receipt
  256 60 3 20 16
  24 3 4 3 0
  false true false 3
  true false false

------------------------------------------------------------------------
-- Snowball / attribution boundaries.
------------------------------------------------------------------------

record MixedActionAttributionBoundary : Set where
  constructor mixed-action-attribution-boundary
  field
    flyCrossRepoCodeIsInternalMethodInspiration : Bool
    flyCodeIsPrimarySourceForGroupTheory : Bool
    c3PrimaryRepresentationSourceStillSeparatelyAttributed : Bool
    DOIRequiredForInternalDASHIImplementation : Bool
    QIDRequiredForImplementationReceipt : Bool
    OEISRequiredWithoutSequenceClaim : Bool
    runtimeAuthorshipEqualsExternalTheoremAuthorship : Bool
open MixedActionAttributionBoundary public

canonicalMixedActionAttributionBoundary : MixedActionAttributionBoundary
canonicalMixedActionAttributionBoundary = mixed-action-attribution-boundary
  true false true false false false false

snowballBoundary : Sources.SnowballAttributionBoundary
snowballBoundary = Sources.canonicalSnowballAttributionBoundary

c3Boundary : C3.StructuredOrbitPromotionBoundary
c3Boundary = C3.canonicalStructuredOrbitPromotionBoundary

------------------------------------------------------------------------
-- New methodological rule: candidate families form fibres too.
------------------------------------------------------------------------

record CandidateFibrePolicy : Set where
  constructor candidate-fibre-policy
  field
    retainDirectionOrGeneratorAlternativesSeparately : Bool
    useStructuralFibresBeforeFinalConsumer : Bool
    intersectIndependentStructuralConstraints : Bool
    freezeCandidateFamilyBeforeGlobalPayoffTest : Bool
    localStructuralSupportImpliesGlobalAction : Bool
    oneFibreSufficesWheneverClassSizeKnown : Bool
open CandidateFibrePolicy public

canonicalCandidateFibrePolicy : CandidateFibrePolicy
canonicalCandidateFibrePolicy = candidate-fibre-policy
  true true true true false false

------------------------------------------------------------------------
-- Next residuals.
------------------------------------------------------------------------

data MixedActionResidual : Set where
  executeExactMixedActionBlob : MixedActionResidual
  executeExactV4FibreBlob : MixedActionResidual
  inferCandidateFibreSetFromProductionObserver : MixedActionResidual
  inferCoRequirementRelationsAcrossMixedActionTypes : MixedActionResidual
  freezeProductionActionFamily : MixedActionResidual
  compareAgainstStructurePreservingActionNulls : MixedActionResidual
  runOnProductionMatrix : MixedActionResidual

firstMixedActionResidual : MixedActionResidual
firstMixedActionResidual = executeExactMixedActionBlob

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data ClassSizeImpliesCyclicGroup : Set where
data PrimaryOperatorSymmetryImpliesConsumerSymmetry : Set where
data MoreStructuralFibresImpliesBetterReduction : Set where
data LocalGeneratorImpliesGlobalSymmetry : Set where
data InternalCodeImpliesPrimaryLiteratureSource : Set where

classSizeDoesNotChooseCyclicGroup : ClassSizeImpliesCyclicGroup → ⊥
classSizeDoesNotChooseCyclicGroup ()

operatorSymmetryDoesNotCreateConsumerSymmetry : PrimaryOperatorSymmetryImpliesConsumerSymmetry → ⊥
operatorSymmetryDoesNotCreateConsumerSymmetry ()

moreFibresDoNotGuaranteeReduction : MoreStructuralFibresImpliesBetterReduction → ⊥
moreFibresDoNotGuaranteeReduction ()

localGeneratorDoesNotCreateGlobalSymmetry : LocalGeneratorImpliesGlobalSymmetry → ⊥
localGeneratorDoesNotCreateGlobalSymmetry ()

internalCodeDoesNotBecomePrimaryLiterature : InternalCodeImpliesPrimaryLiteratureSource → ⊥
internalCodeDoesNotBecomePrimaryLiterature ()
