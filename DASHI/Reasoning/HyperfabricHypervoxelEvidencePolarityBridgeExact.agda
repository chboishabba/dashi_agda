module DASHI.Reasoning.HyperfabricHypervoxelEvidencePolarityBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Algebra.ClaimIndexedEvidencePolarityExact as Indexed
import DASHI.Foundations.RecursiveRadixHypervoxel as Hypervoxel
import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric

------------------------------------------------------------------------
-- Hyperfabric / hypervoxel evidence geometry.
--
-- TypedHyperfabric supplies local stalks, restrictions, provenance and
-- compatibility.  Claim evidence additionally carries an OppositionDescriptor,
-- so a local counter-view, reversal, inverse or logical negation cannot be
-- conflated merely because all occupy the second information coordinate.
-- RecursiveRadixHypervoxel remains a separate geometric polarity fibre.
------------------------------------------------------------------------

HypervoxelClaimEvidence :
  (rank depth : Nat) →
  Indexed.OppositionDescriptor String →
  Hypervoxel.LiftedAddress rank depth →
  Set
HypervoxelClaimEvidence rank depth opposition site =
  Indexed.ClaimFibreEvidence
    String
    (Hypervoxel.LiftedAddress rank depth)
    opposition
    site

centralFlipIsVerticalAtBase :
  ∀ {rank depth} (site : Hypervoxel.LiftedAddress rank depth) →
  Hypervoxel.projectLiftedAddress (Hypervoxel.centralFlip site)
  ≡ Hypervoxel.projectLiftedAddress site
centralFlipIsVerticalAtBase = Hypervoxel.projectCentralFlipInvariant

record EvidenceHyperfabricInstantiation
    (Vertex Edge Claim Context : Set) : Set₁ where
  field
    fabric : Hyperfabric.TypedHyperfabric Vertex Edge
    oppositionAt : Vertex → Indexed.OppositionDescriptor Claim
    contextAt : Vertex → Context
    localEvidence :
      (vertex : Vertex) →
      Indexed.ClaimFibreEvidence
        Claim Context (oppositionAt vertex) (contextAt vertex)

open EvidenceHyperfabricInstantiation public

record HyperfabricHypervoxelEvidenceBoundary : Set where
  field
    evidenceCanLiveInTypedStalks : Bool
    localEvidenceRequiresClaimContextIndex : Bool
    localEvidenceRequiresOppositionRoleIndex : Bool
    verticalFibreMotionCanBeBaseInvisible : Bool
    centreBlindDescentRequiresInvariance : Bool
    hyperfabricAutomaticallyDiagnosesClaimed : Bool
    polarityFibreEqualsLogicalNegationClaimed : Bool
    polarityFibreEqualsTernaryAxisClaimed : Bool

canonicalHyperfabricHypervoxelEvidenceBoundary :
  HyperfabricHypervoxelEvidenceBoundary
canonicalHyperfabricHypervoxelEvidenceBoundary = record
  { evidenceCanLiveInTypedStalks = true
  ; localEvidenceRequiresClaimContextIndex = true
  ; localEvidenceRequiresOppositionRoleIndex = true
  ; verticalFibreMotionCanBeBaseInvisible = true
  ; centreBlindDescentRequiresInvariance = true
  ; hyperfabricAutomaticallyDiagnosesClaimed = false
  ; polarityFibreEqualsLogicalNegationClaimed = false
  ; polarityFibreEqualsTernaryAxisClaimed = false
  }

hyperfabricAuthorityBoundaryReused : Hyperfabric.TypedHyperfabricAuthorityBoundary
hyperfabricAuthorityBoundaryReused = Hyperfabric.canonicalTypedHyperfabricAuthorityBoundary

hypervoxelAuthorityBoundaryReused : Hypervoxel.HypervoxelAuthorityBoundary
hypervoxelAuthorityBoundaryReused = Hypervoxel.canonicalHypervoxelAuthorityBoundary
