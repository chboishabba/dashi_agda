{-# OPTIONS --safe #-}
module DASHI.AnimalCommunication.ZKAttestation where

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.AnimalCommunication.PoseMDL

-- This module specifies the relation that a zero-knowledge implementation
-- must prove.  It does not postulate cryptographic hiding, binding, soundness,
-- or zero knowledge: those belong to a concrete proof-system instance.
record CommitmentFamily
  (V T P M S Digest : Set) : Set₁ where
  field
    commitVideo   : V → Digest
    commitTrack   : T → Digest
    commitPose    : P → Digest
    commitProgram : M → Digest
    commitSummary : S → Digest

record PipelineVersions : Set where
  field
    extractorVersion : Nat
    poseVersion       : Nat
    compilerVersion   : Nat
    dictionaryVersion : Nat
    publisherVersion  : Nat

record DogVideoPipeline (M : PoseMDLSpec) : Set₁ where
  open PoseMDLSpec M
  field
    Video DogTrack : Set

    extractDog : Video → DogTrack
    estimatePose : DogTrack → PoseRibbon

    VideoAdmissible : Video → Set
    TrackAdmissible : DogTrack → Set
    PoseAdmissible  : PoseRibbon → Set

    quality : PoseRibbon → Nat
    threshold : Nat

record PrivateTrace (M : PoseMDLSpec) (E : DogVideoPipeline M) : Set where
  open PoseMDLSpec M
  open DogVideoPipeline E
  field
    video      : Video
    dogTrack   : DogTrack
    poseRibbon : PoseRibbon
    dictionary : Dictionary
    program    : MotifProgram
    summary    : Summary

record StageCommitments
  {M : PoseMDLSpec}
  (E : DogVideoPipeline M)
  (Digest : Set) : Set where
  open PoseMDLSpec M
  open DogVideoPipeline E
  field
    videoCommitment   : Digest
    trackCommitment   : Digest
    poseCommitment    : Digest
    programCommitment : Digest
    summaryCommitment : Digest

record PublicClaim
  {M : PoseMDLSpec}
  (E : DogVideoPipeline M)
  (Digest : Set) : Set where
  open PoseMDLSpec M
  field
    commitments : StageCommitments E Digest
    versions    : PipelineVersions
    releasedSummary : Summary
    residualBudget  : Nat

-- The complete staged relation:
-- C0 video -> C1 dog track -> C2 pose ribbon -> C3 motif program -> C4 summary.
-- A concrete prover may prove this monolithically or recursively compose the
-- five stage proofs.
record Attests
  {M : PoseMDLSpec}
  (E : DogVideoPipeline M)
  {Digest : Set}
  (C : CommitmentFamily
    (DogVideoPipeline.Video E)
    (DogVideoPipeline.DogTrack E)
    (PoseMDLSpec.PoseRibbon M)
    (PoseMDLSpec.MotifProgram M)
    (PoseMDLSpec.Summary M)
    Digest)
  (claim : PublicClaim E Digest)
  (trace : PrivateTrace M E) : Set where

  open PoseMDLSpec M
  open DogVideoPipeline E
  open CommitmentFamily C
  open PublicClaim claim
  open StageCommitments commitments
  open PrivateTrace trace

  field
    c0 : commitVideo video ≡ videoCommitment
    c1 : commitTrack dogTrack ≡ trackCommitment
    c2 : commitPose poseRibbon ≡ poseCommitment
    c3 : commitProgram program ≡ programCommitment
    c4 : commitSummary summary ≡ summaryCommitment

    π01 : extractDog video ≡ dogTrack
    π12 : estimatePose dogTrack ≡ poseRibbon
    π23 : compile dictionary (canonicalize poseRibbon) ≡ program
    π34 : publish program ≡ summary

    video-admissible : VideoAdmissible video
    track-admissible : TrackAdmissible dogTrack
    pose-admissible  : PoseAdmissible poseRibbon
    quality-gate     : threshold ≤ quality poseRibbon
    residual-gate :
      residualCost (canonicalize poseRibbon) program ≤ residualBudget
    public-output : summary ≡ releasedSummary

-- The public verifier's mathematical statement is existential: there is a
-- private trace satisfying the fixed relation.  The witness itself need not
-- be revealed by a cryptographic realization.
VerifiedClaim :
  {M : PoseMDLSpec} →
  (E : DogVideoPipeline M) →
  {Digest : Set} →
  (C : CommitmentFamily
    (DogVideoPipeline.Video E)
    (DogVideoPipeline.DogTrack E)
    (PoseMDLSpec.PoseRibbon M)
    (PoseMDLSpec.MotifProgram M)
    (PoseMDLSpec.Summary M)
    Digest) →
  PublicClaim E Digest → Set
VerifiedClaim {M} E C claim = Σ (PrivateTrace M E) (Attests E C claim)
