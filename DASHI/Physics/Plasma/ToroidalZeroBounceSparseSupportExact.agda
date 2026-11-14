module DASHI.Physics.Plasma.ToroidalZeroBounceSparseSupportExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as T27
import DASHI.Physics.Plasma.Ternary27SpectralGeometryCarrierExact as Carrier
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce

------------------------------------------------------------------------
-- SPARSE SUPPORT OVER THE TERNARY-27 SEARCH CHART
--
-- A support patch selects the subset of the literal 27 search coordinates that
-- are allowed to carry nonzero coefficients.  Support size / description
-- length ranks candidates only after hard physical admissibility and consumer
-- adequacy are paid, exactly following the repo-native MDL owner.
------------------------------------------------------------------------

record SupportPatch : Set₁ where
  constructor support-patch
  field
    Active : T27.Ternary27Point → Set
    supportSize : Nat
    finiteSupportReceipt : Set
    patchReference : String

open SupportPatch public

record SparseSupportRealization
    (Coefficient PhysicalPerturbation : Set) : Set₁ where
  constructor sparse-support-realization
  field
    patch : SupportPatch
    realization : Carrier.Ternary27PhysicalRealization Coefficient PhysicalPerturbation
    inactiveCoordinatesAreZeroReceipt : Set
    samePhysicalRealizationMapReceipt : Set
    sameC3SpectralChartReceipt : Set
    realizationReference : String

open SparseSupportRealization public

record SparseSupportConsumerAdequacy
    (population : ZeroBounce.DeclaredParticlePopulation)
    (patch : SupportPatch) : Set₁ where
  constructor sparse-support-consumer-adequacy
  field
    zeroBouncePreservedReceipt : ZeroBounce.ZeroBounceReceipt population
    constantMagnitudeConsumerReceipt : Set
    geodesicCurvatureConsumerReceipt : Set
    divergenceFreeConsumerReceipt : Set
    nestedSurfaceConsumerReceipt : Set
    finiteOrbitWidthConsumerReceipt : Set
    energeticParticleConsumerReceipt : Set
    bestKnownReferenceConsumerReceipt : Set
    sameComparisonChartReceipt : Set
    consumerReference : String

open SparseSupportConsumerAdequacy public

record SparseSupportMDLInstantiation : Set₁ where
  constructor sparse-support-mdl-instantiation
  field
    problem : MDL.ConsumerMDLProblem
    supportPatchToModelReceipt : Set
    descriptionLengthIsSupportCodingReceipt : Set
    admissibilityIncludesHardPhysicsReceipt : Set
    consumerAdequacyIncludesOrbitAndReferenceReceipt : Set
    instantiationReference : String

open SparseSupportMDLInstantiation public

record SparseSupportBoundary : Set where
  constructor sparse-support-boundary
  field
    shortestSupportWinsWithoutPhysics : Bool
    shortestSupportWinsWithoutPhysicsIsFalse :
      shortestSupportWinsWithoutPhysics ≡ false

    zeroingCoefficientAutomaticallyPreservesConsumers : Bool
    zeroingCoefficientAutomaticallyPreservesConsumersIsFalse :
      zeroingCoefficientAutomaticallyPreservesConsumers ≡ false

    consumerFailureMayReopenSupportLocally : Bool
    consumerFailureMayReopenSupportLocallyIsTrue :
      consumerFailureMayReopenSupportLocally ≡ true

    sparseSupportIsPhysicalTruth : Bool
    sparseSupportIsPhysicalTruthIsFalse :
      sparseSupportIsPhysicalTruth ≡ false

canonicalSparseSupportBoundary : SparseSupportBoundary
canonicalSparseSupportBoundary =
  sparse-support-boundary
    false refl
    false refl
    true refl
    false refl

pythonReplayReference : String
pythonReplayReference =
  "scripts/ternary27_sparse_support.py / scripts/test_ternary27_sparse_support.py"
