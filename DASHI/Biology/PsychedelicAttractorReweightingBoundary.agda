module DASHI.Biology.PsychedelicAttractorReweightingBoundary where

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

import DASHI.Geometry.SSP369Ultrametric as U369
import DASHI.Core.RelationalHypervoxelBraidCore as Hypervoxel
import DASHI.Biology.PredictiveMetastabilityTraumaBridge as Predictive

------------------------------------------------------------------------
-- Psychedelic attractor/routing reweighting boundary.
--
-- The formal claim is deliberately modest: a perturbation may alter relative
-- routing costs, prior precision, modular segregation, and reachable state
-- repertoire while preserving a structured transition system.  This is not a
-- treatment theorem, a universal pharmacological law, or evidence that every
-- vision has a fixed symbolic dictionary.
--
-- Source-facing references:
--
-- Robin Carhart-Harris and Karl Friston,
-- "REBUS and the Anarchic Brain: Toward a Unified Model of the Brain Action
-- of Psychedelics", DOI 10.1124/pr.118.017160.
--
-- Robin Carhart-Harris et al.,
-- "The entropic brain: a theory of conscious states informed by
-- neuroimaging research with psychedelic drugs",
-- DOI 10.3389/fnhum.2014.00020.
--
-- Enzo Tagliazucchi et al.,
-- "Enhanced repertoire of brain dynamical states during the psychedelic
-- experience", DOI 10.1002/hbm.22562.

DepthTwoAddress : Set
DepthTwoAddress = U369.Address (suc (suc zero))

habitualAddress : DepthTwoAddress
habitualAddress =
  U369.digit3 vcons U369.digit3 vcons vnil

nearbyAddress : DepthTwoAddress
nearbyAddress =
  U369.digit3 vcons U369.digit6 vcons vnil

crossBranchAddress : DepthTwoAddress
crossBranchAddress =
  U369.digit9 vcons U369.digit9 vcons vnil

habitualSelfDistanceZero :
  U369.distance habitualAddress habitualAddress ≡ zero
habitualSelfDistanceZero =
  U369.distance-self-zero habitualAddress

nearbyAddressDistanceOne :
  U369.distance habitualAddress nearbyAddress ≡ suc zero
nearbyAddressDistanceOne = refl

crossBranchAddressDistanceTwo :
  U369.distance habitualAddress crossBranchAddress ≡ suc (suc zero)
crossBranchAddressDistanceTwo = refl

record AttractorCostProfile : Set where
  constructor attractorCostProfile
  field
    habitualCost : Nat
    nearbyCost : Nat
    crossBranchCost : Nat

open AttractorCostProfile public

baselineAttractorCosts : AttractorCostProfile
baselineAttractorCosts =
  attractorCostProfile zero (suc zero) (suc (suc zero))

reweightedAttractorCosts : AttractorCostProfile
reweightedAttractorCosts =
  attractorCostProfile (suc zero) (suc zero) (suc zero)

habitualBasinIsShallower :
  habitualCost baselineAttractorCosts
  ≤
  habitualCost reweightedAttractorCosts
habitualBasinIsShallower = z≤n

crossBranchCostIsLower :
  crossBranchCost reweightedAttractorCosts
  ≤
  crossBranchCost baselineAttractorCosts
crossBranchCostIsLower = s≤s z≤n

record RoutingRegime : Set where
  constructor routingRegime
  field
    routingThreshold : Nat
    modularSegregation : Nat
    reachableRepertoire : Nat
    highLevelPriorPrecision : Nat

open RoutingRegime public

baselineRoutingRegime : RoutingRegime
baselineRoutingRegime =
  routingRegime
    (suc (suc zero))
    (suc (suc zero))
    (suc zero)
    (suc (suc zero))

reweightedRoutingRegime : RoutingRegime
reweightedRoutingRegime =
  routingRegime
    (suc zero)
    (suc zero)
    (suc (suc zero))
    (suc zero)

routingThresholdIsLower :
  routingThreshold reweightedRoutingRegime
  ≤
  routingThreshold baselineRoutingRegime
routingThresholdIsLower = s≤s z≤n

modularSegregationIsLower :
  modularSegregation reweightedRoutingRegime
  ≤
  modularSegregation baselineRoutingRegime
modularSegregationIsLower = s≤s z≤n

reachableRepertoireIsLarger :
  reachableRepertoire baselineRoutingRegime
  ≤
  reachableRepertoire reweightedRoutingRegime
reachableRepertoireIsLarger = s≤s z≤n

highLevelPriorPrecisionIsLower :
  highLevelPriorPrecision reweightedRoutingRegime
  ≤
  highLevelPriorPrecision baselineRoutingRegime
highLevelPriorPrecisionIsLower = s≤s z≤n

------------------------------------------------------------------------
-- Recurrent motifs are represented as persistent transition modes, not as
-- random strings and not as a universal symbolic dictionary.

data VisionMotif : Set where
  geometricMotif : VisionMotif
  agentMotif : VisionMotif
  boundaryDissolutionMotif : VisionMotif

nextMotif : VisionMotif → VisionMotif
nextMotif geometricMotif = agentMotif
nextMotif agentMotif = boundaryDissolutionMotif
nextMotif boundaryDissolutionMotif = geometricMotif

motifCycleReturns :
  nextMotif (nextMotif (nextMotif geometricMotif))
  ≡
  geometricMotif
motifCycleReturns = refl

record StructuredVisionRegime : Set where
  constructor structuredVisionRegime
  field
    motif : VisionMotif
    successor : VisionMotif
    successorIsGenerated : successor ≡ nextMotif motif
    unstructuredNoiseOnly : Bool
    unstructuredNoiseOnlyIsFalse : unstructuredNoiseOnly ≡ false

canonicalStructuredVisionRegime : StructuredVisionRegime
canonicalStructuredVisionRegime =
  structuredVisionRegime
    geometricMotif
    agentMotif
    refl
    false
    refl

record PsychedelicAttractorBoundary : Set where
  constructor psychedelicAttractorBoundary
  field
    predictiveBridge :
      Predictive.PredictiveMetastabilityTraumaBridge

    hypervoxelGovernance :
      Hypervoxel.HypervoxelGovernance

    baselineCosts : AttractorCostProfile
    reweightedCosts : AttractorCostProfile
    baselineRouting : RoutingRegime
    reweightedRouting : RoutingRegime
    structuredVision : StructuredVisionRegime

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    treatmentProtocolPromoted : Bool
    treatmentProtocolPromotedIsFalse :
      treatmentProtocolPromoted ≡ false

    recoveredMemoryAuthorityPromoted : Bool
    recoveredMemoryAuthorityPromotedIsFalse :
      recoveredMemoryAuthorityPromoted ≡ false

    universalSymbolDictionaryPromoted : Bool
    universalSymbolDictionaryPromotedIsFalse :
      universalSymbolDictionaryPromoted ≡ false

    entropyBiomarkerTreatedAsSettled : Bool
    entropyBiomarkerTreatedAsSettledIsFalse :
      entropyBiomarkerTreatedAsSettled ≡ false

open PsychedelicAttractorBoundary public

canonicalPsychedelicAttractorBoundary : PsychedelicAttractorBoundary
canonicalPsychedelicAttractorBoundary =
  psychedelicAttractorBoundary
    Predictive.canonicalPredictiveMetastabilityTraumaBridge
    Hypervoxel.canonicalHypervoxelGovernance
    baselineAttractorCosts
    reweightedAttractorCosts
    baselineRoutingRegime
    reweightedRoutingRegime
    canonicalStructuredVisionRegime
    true refl
    false refl
    false refl
    false refl
    false refl
