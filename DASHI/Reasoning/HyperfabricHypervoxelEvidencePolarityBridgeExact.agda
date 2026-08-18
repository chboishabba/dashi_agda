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
-- TypedHyperfabric already supplies local stalks, restriction maps,
-- provenance, compatible global sections and explicit obstructions.
-- RecursiveRadixHypervoxel already supplies a ternary base address plus a
-- polarity fibre, with centralFlip moving vertically while the base projection
-- is unchanged.  Claim-indexed evidence belongs in those local/fine fibres;
-- centre-blind descent still requires the existing invariance witness.
------------------------------------------------------------------------

HypervoxelClaimEvidence :
  (rank depth : Nat) →
  String →
  Hypervoxel.LiftedAddress rank depth →
  Set
HypervoxelClaimEvidence rank depth claim site =
  Indexed.ClaimFibreEvidence
    String
    (Hypervoxel.LiftedAddress rank depth)
    claim
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
    claimAt : Vertex → Claim
    contextAt : Vertex → Context
    localEvidence :
      (vertex : Vertex) →
      Indexed.ClaimFibreEvidence
        Claim Context (claimAt vertex) (contextAt vertex)

open EvidenceHyperfabricInstantiation public

record HyperfabricHypervoxelEvidenceBoundary : Set where
  field
    evidenceCanLiveInTypedStalks : Bool
    localEvidenceRequiresClaimContextIndex : Bool
    verticalFibreMotionCanBeBaseInvisible : Bool
    centreBlindDescentRequiresInvariance : Bool
    hyperfabricAutomaticallyDiagnosesClaimed : Bool
    polarityFibreEqualsTernaryAxisClaimed : Bool

canonicalHyperfabricHypervoxelEvidenceBoundary :
  HyperfabricHypervoxelEvidenceBoundary
canonicalHyperfabricHypervoxelEvidenceBoundary = record
  { evidenceCanLiveInTypedStalks = true
  ; localEvidenceRequiresClaimContextIndex = true
  ; verticalFibreMotionCanBeBaseInvisible = true
  ; centreBlindDescentRequiresInvariance = true
  ; hyperfabricAutomaticallyDiagnosesClaimed = false
  ; polarityFibreEqualsTernaryAxisClaimed = false
  }

hyperfabricAuthorityBoundaryReused : Hyperfabric.TypedHyperfabricAuthorityBoundary
hyperfabricAuthorityBoundaryReused = Hyperfabric.canonicalTypedHyperfabricAuthorityBoundary

hypervoxelAuthorityBoundaryReused : Hypervoxel.HypervoxelAuthorityBoundary
hypervoxelAuthorityBoundaryReused = Hypervoxel.canonicalHypervoxelAuthorityBoundary
