{-# OPTIONS --safe #-}
module DASHI.AnimalCommunication.DogVideoSystem where

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)
open import Data.Product using (Σ)

open import DASHI.AnimalCommunication.PoseMDL
open import DASHI.AnimalCommunication.ZKAttestation

-- O/R/C/S/L/P/G/F specialization for privacy-preserving animal
-- communication research.
--
-- O : operator / accountable processing authority
-- R : rules, versions, admissibility policy, and release policy
-- C : private clip carrier
-- S : extraction trace / state ribbon
-- L : learned or fixed motif lexicon
-- P : bounded public claim
-- G : residual and uncertainty budget
-- F : verification relation
record DogVideoORCSLPGF : Set₂ where
  field
    Operator Rules Digest : Set
    operator : Operator
    rules    : Rules

    mdl      : PoseMDLSpec
    pipeline : DogVideoPipeline mdl

    commitments : CommitmentFamily
      (DogVideoPipeline.Video pipeline)
      (DogVideoPipeline.DogTrack pipeline)
      (PoseMDLSpec.PoseRibbon mdl)
      (PoseMDLSpec.MotifProgram mdl)
      (PoseMDLSpec.Summary mdl)
      Digest

    versions : PipelineVersions

  Clip : Set
  Clip = DogVideoPipeline.Video pipeline

  State : Set
  State = PrivateTrace mdl pipeline

  Lexicon : Set
  Lexicon = PoseMDLSpec.Dictionary mdl

  Claim : Set
  Claim = PublicClaim pipeline Digest

  Gap : Set
  Gap = Nat

  F : Claim → Set
  F claim = VerifiedClaim pipeline commitments claim

open DogVideoORCSLPGF public

-- Split trust boundary used by the practical rollout:
--
--   mediaAttestation : raw video -> committed pose ribbon
--   compilerProof    : private pose ribbon -> MDL program -> bounded summary
--
-- The first may initially be discharged by a signed extractor, TEE, sampled
-- audit, or a future neural-network proof circuit.  The second is intended to
-- be deterministic and directly formal/proof-system friendly.
record SplitTrustBoundary (S : DogVideoORCSLPGF) : Set₁ where
  open DogVideoORCSLPGF S
  open PoseMDLSpec mdl
  open DogVideoPipeline pipeline
  field
    MediaAttestation : Video → PoseRibbon → Set
    CompilerProof : PoseRibbon → Dictionary → Summary → Nat → Set

    media-sound :
      ∀ video pose →
      MediaAttestation video pose →
      VideoAdmissible video

    compiler-residual-bounded :
      ∀ pose dictionary summary budget →
      CompilerProof pose dictionary summary budget →
      Σ MotifProgram
        (λ program → residualCost (canonicalize pose) program ≤ budget)

open SplitTrustBoundary public

-- Bounded semantics discipline: cryptographic verification establishes only
-- that a public predicate holds of the released summary.  It does not turn
-- that predicate into an ontological claim about what the dog 'really means'.
record BoundedSemanticProbe (S : DogVideoORCSLPGF) : Set₁ where
  open DogVideoORCSLPGF S
  open PoseMDLSpec mdl
  field
    Probe : Set
    holds : Probe → Summary → Set
    releaseAllowed : Probe → Summary → Set
    bounded : ∀ probe summary → holds probe summary → releaseAllowed probe summary

open BoundedSemanticProbe public

-- Cohort release boundary.  The aggregate itself stays abstract so that
-- concrete instances may use counts, histograms, transition matrices, or
-- differential-private statistics.  Every included claim must nevertheless
-- carry the same verification relation F.
record VerifiedCohort (S : DogVideoORCSLPGF) : Set₁ where
  open DogVideoORCSLPGF S
  field
    Index Aggregate : Set
    claimAt : Index → Claim
    verifiedAt : ∀ i → F (claimAt i)
    aggregate : Aggregate

open VerifiedCohort public
