module DASHI.Reasoning.DevelopmentalAttunementPNFBridge where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Biology.PredictiveMetastabilityTraumaBridge as Predictive
import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Cognition.PNF.TraumaMemoryHypervoxelBridge as TraumaPNF
import DASHI.Core.RelationalHypervoxelBraidCore as RelationalHypervoxel
import DASHI.FullRelationalFlowRepairHyperfabric as FullRepair
import DASHI.Reasoning.AttractorAlignedBranchSelection as Selection
import DASHI.Reasoning.RelationalProcessMemoryHyperfabric as Process
import DASHI.Reasoning.RelationalStateCore as Core

------------------------------------------------------------------------
-- Developmental abstraction.
--
-- This module models a child-parent or dependent-caregiver relation without
-- identifying the carrier with any named family.  The exact finite theorem is
-- deliberately about response order: equal attention quantity and an equal
-- multiset of response kinds can still have unequal fragmentation burden.
--
-- Empirical provenance and DOI metadata live in
-- RelationalFormalismSourceAtlas.  Limited-bedding, maternal-signal,
-- synchrony and still-face studies are used only as bounded structural
-- sources; no animal paradigm or finite trace diagnoses a person or proves a
-- causal account of a particular family.
------------------------------------------------------------------------

data DevelopmentalRelation : Set where
  parentChildRelation caregiverDependentRelation : DevelopmentalRelation

record DevelopmentalDyad : Set where
  constructor developmentalDyad
  field
    relationKind : DevelopmentalRelation
    caregiver child : Core.Participant
    relationReceipt : String

open DevelopmentalDyad public

------------------------------------------------------------------------
-- Response alphabet and exact fragmentation arithmetic.
------------------------------------------------------------------------

data ResponseSignal : Set where
  contingentUptake : ResponseSignal
  associativeDisplacement : ResponseSignal
  solutionSubstitution : ResponseSignal
  intrusiveNormalisation : ResponseSignal
  noResponse : ResponseSignal

signalCode : ResponseSignal → Nat
signalCode contingentUptake = 0
signalCode associativeDisplacement = 1
signalCode solutionSubstitution = 2
signalCode intrusiveNormalisation = 3
signalCode noResponse = 4

natEq : Nat → Nat → Bool
natEq zero zero = true
natEq zero (suc n) = false
natEq (suc m) zero = false
natEq (suc m) (suc n) = natEq m n

sameSignal : ResponseSignal → ResponseSignal → Bool
sameSignal left right = natEq (signalCode left) (signalCode right)

attentionMass : List ResponseSignal → Nat
attentionMass [] = zero
attentionMass (noResponse ∷ rest) = attentionMass rest
attentionMass (_ ∷ rest) = suc (attentionMass rest)

uptakeMass : List ResponseSignal → Nat
uptakeMass [] = zero
uptakeMass (contingentUptake ∷ rest) = suc (uptakeMass rest)
uptakeMass (_ ∷ rest) = uptakeMass rest

switchCount : List ResponseSignal → Nat
switchCount [] = zero
switchCount (_ ∷ []) = zero
switchCount (left ∷ right ∷ rest) with sameSignal left right
... | true = switchCount (right ∷ rest)
... | false = suc (switchCount (right ∷ rest))

signalDrift : ResponseSignal → Selection.AttractorDrift
signalDrift contingentUptake =
  Selection.attractorDrift Selection.towardAttractor 2
signalDrift associativeDisplacement =
  Selection.attractorDrift Selection.awayFromAttractor 1
signalDrift solutionSubstitution =
  Selection.attractorDrift Selection.awayFromAttractor 1
signalDrift intrusiveNormalisation =
  Selection.attractorDrift Selection.awayFromAttractor 2
signalDrift noResponse =
  Selection.attractorDrift Selection.neutralDrift 0

traceBenefit : List ResponseSignal → Nat
traceBenefit [] = zero
traceBenefit (signal ∷ rest) =
  Selection.driftBenefit (signalDrift signal) + traceBenefit rest

traceBaseBurden : List ResponseSignal → Nat
traceBaseBurden [] = zero
traceBaseBurden (signal ∷ rest) =
  Selection.driftBurden (signalDrift signal) + traceBaseBurden rest

traceTotalBurden : List ResponseSignal → Nat
traceTotalBurden trace = traceBaseBurden trace + switchCount trace

stableTrace : List ResponseSignal
stableTrace =
  contingentUptake
  ∷ contingentUptake
  ∷ intrusiveNormalisation
  ∷ intrusiveNormalisation
  ∷ []

fragmentedTrace : List ResponseSignal
fragmentedTrace =
  contingentUptake
  ∷ intrusiveNormalisation
  ∷ contingentUptake
  ∷ intrusiveNormalisation
  ∷ []

stableAttentionIsFour : attentionMass stableTrace ≡ 4
stableAttentionIsFour = refl

fragmentedAttentionIsFour : attentionMass fragmentedTrace ≡ 4
fragmentedAttentionIsFour = refl

stableUptakeIsTwo : uptakeMass stableTrace ≡ 2
stableUptakeIsTwo = refl

fragmentedUptakeIsTwo : uptakeMass fragmentedTrace ≡ 2
fragmentedUptakeIsTwo = refl

stableSwitchCountIsOne : switchCount stableTrace ≡ 1
stableSwitchCountIsOne = refl

fragmentedSwitchCountIsThree : switchCount fragmentedTrace ≡ 3
fragmentedSwitchCountIsThree = refl

stableBenefitIsFour : traceBenefit stableTrace ≡ 4
stableBenefitIsFour = refl

fragmentedBenefitIsFour : traceBenefit fragmentedTrace ≡ 4
fragmentedBenefitIsFour = refl

stableBaseBurdenIsFour : traceBaseBurden stableTrace ≡ 4
stableBaseBurdenIsFour = refl

fragmentedBaseBurdenIsFour : traceBaseBurden fragmentedTrace ≡ 4
fragmentedBaseBurdenIsFour = refl

stableTotalBurdenIsFive : traceTotalBurden stableTrace ≡ 5
stableTotalBurdenIsFive = refl

fragmentedTotalBurdenIsSeven : traceTotalBurden fragmentedTrace ≡ 7
fragmentedTotalBurdenIsSeven = refl

record SameQuantityGreaterFragmentation
    (stable fragmented : List ResponseSignal) : Set where
  constructor sameQuantityGreaterFragmentation
  field
    sameAttention : attentionMass stable ≡ attentionMass fragmented
    sameUptakeQuantity : uptakeMass stable ≡ uptakeMass fragmented
    sameAttractorBenefit : traceBenefit stable ≡ traceBenefit fragmented
    sameBaseBurden : traceBaseBurden stable ≡ traceBaseBurden fragmented
    twoAdditionalSwitches :
      switchCount fragmented ≡ suc (suc (switchCount stable))
    twoAdditionalTotalBurden :
      traceTotalBurden fragmented ≡ suc (suc (traceTotalBurden stable))

open SameQuantityGreaterFragmentation public

canonicalFragmentationWitness :
  SameQuantityGreaterFragmentation stableTrace fragmentedTrace
canonicalFragmentationWitness =
  sameQuantityGreaterFragmentation
    refl
    refl
    refl
    refl
    refl
    refl

------------------------------------------------------------------------
-- Shared-state / PNF memory carrier.
--
-- `responseTrace` remains ordered.  Reducing it to attentionMass would erase
-- the exact distinction proved above.  PNF comparison, rupture and capacity
-- are retained as separate fibres rather than compressed into one outcome.
------------------------------------------------------------------------

record DevelopmentalInteractionEpisode : Set where
  constructor developmentalInteractionEpisode
  field
    dyad : DevelopmentalDyad
    childContribution : Core.Contribution
    responseTrace : List ResponseSignal
    sharedStateBefore sharedStateAfter : Core.SharedState
    pnfComparison : PNF.ComparisonResult
    rupture : Core.RuptureStatus
    childCapacity : Core.CapacityState
    causalEdgeFromResponseToWithdrawalRetained : Bool
    episodeReceipt : String

open DevelopmentalInteractionEpisode public

record DevelopmentalTraceMemory : Set where
  constructor developmentalTraceMemory
  field
    episode : DevelopmentalInteractionEpisode
    orderedTraceRetained : Bool
    contributionProvenanceRetained : Bool
    unresolvedRuptureRetained : Bool
    oldVersionRetained : Bool
    memoryReceipt : String

open DevelopmentalTraceMemory public

------------------------------------------------------------------------
-- Explicit reuse of the repository's existing trauma / PNF / hyperfabric
-- authorities.  This is a cross-pollination object, not a new clinical lane.
------------------------------------------------------------------------

record ExistingTraumaPNFHyperformalismReuse : Setω where
  field
    pnfProducerBoundary : PNF.PNFProducerBoundary
    pnfProducerBoundaryIsCanonical :
      pnfProducerBoundary ≡ PNF.canonicalPNFProducerBoundary

    predictiveTraumaBridge : Predictive.PredictiveMetastabilityTraumaBridge
    predictiveTraumaBridgeIsCanonical :
      predictiveTraumaBridge
      ≡ Predictive.canonicalPredictiveMetastabilityTraumaBridge

    traumaMemoryHypervoxelBoundary :
      TraumaPNF.TraumaMemoryHypervoxelAuthorityBoundary
    traumaMemoryHypervoxelBoundaryIsCanonical :
      traumaMemoryHypervoxelBoundary
      ≡ TraumaPNF.canonicalTraumaMemoryHypervoxelAuthorityBoundary

    relationalHypervoxelGovernance :
      RelationalHypervoxel.HypervoxelGovernance
    relationalHypervoxelGovernanceIsCanonical :
      relationalHypervoxelGovernance
      ≡ RelationalHypervoxel.canonicalHypervoxelGovernance

    processMemoryBoundary : Process.ProcessMemoryAuthorityBoundary
    processMemoryBoundaryIsCanonical :
      processMemoryBoundary ≡ Process.canonicalProcessMemoryAuthorityBoundary

    fullRelationalRepairHyperformalism :
      FullRepair.FullRelationalFlowRepairHyperfabric
    fullRelationalRepairHyperformalismIsCanonical :
      fullRelationalRepairHyperformalism
      ≡ FullRepair.canonicalFullRelationalFlowRepairHyperfabric

canonicalExistingTraumaPNFHyperformalismReuse :
  ExistingTraumaPNFHyperformalismReuse
canonicalExistingTraumaPNFHyperformalismReuse = record
  { pnfProducerBoundary = PNF.canonicalPNFProducerBoundary
  ; pnfProducerBoundaryIsCanonical = refl
  ; predictiveTraumaBridge =
      Predictive.canonicalPredictiveMetastabilityTraumaBridge
  ; predictiveTraumaBridgeIsCanonical = refl
  ; traumaMemoryHypervoxelBoundary =
      TraumaPNF.canonicalTraumaMemoryHypervoxelAuthorityBoundary
  ; traumaMemoryHypervoxelBoundaryIsCanonical = refl
  ; relationalHypervoxelGovernance =
      RelationalHypervoxel.canonicalHypervoxelGovernance
  ; relationalHypervoxelGovernanceIsCanonical = refl
  ; processMemoryBoundary = Process.canonicalProcessMemoryAuthorityBoundary
  ; processMemoryBoundaryIsCanonical = refl
  ; fullRelationalRepairHyperformalism =
      FullRepair.canonicalFullRelationalFlowRepairHyperfabric
  ; fullRelationalRepairHyperformalismIsCanonical = refl
  }

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record DevelopmentalAttunementAuthorityBoundary : Set where
  field
    equalAttentionImpliesEqualAttunement : Bool
    fragmentationAloneDiagnosesTrauma : Bool
    animalModelDirectlyIdentifiesHumanCause : Bool
    caregiverIntentErasesChildImpact : Bool
    childSilenceAutomaticallyMeansAssent : Bool
    oneFiniteTraceEstablishesStableCharacter : Bool
    relationalCarrierPromotesClinicalFinding : Bool
    boundaryNote : String

canonicalDevelopmentalAttunementAuthorityBoundary :
  DevelopmentalAttunementAuthorityBoundary
canonicalDevelopmentalAttunementAuthorityBoundary = record
  { equalAttentionImpliesEqualAttunement = false
  ; fragmentationAloneDiagnosesTrauma = false
  ; animalModelDirectlyIdentifiesHumanCause = false
  ; caregiverIntentErasesChildImpact = false
  ; childSilenceAutomaticallyMeansAssent = false
  ; oneFiniteTraceEstablishesStableCharacter = false
  ; relationalCarrierPromotesClinicalFinding = false
  ; boundaryNote =
      "The exact theorem separates attention quantity from temporal pattern and switching burden. It does not diagnose a caregiver or child, infer motive, or transport an animal paradigm into a particular human causal finding."
  }
