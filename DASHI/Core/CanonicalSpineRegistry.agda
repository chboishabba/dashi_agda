{-# OPTIONS --safe #-}
module DASHI.Core.CanonicalSpineRegistry where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Canonical owner registry.
--
-- This is a checked repository-governance surface: new bridges should import
-- these owners instead of defining parallel trit, residual, MDL, ultrametric,
-- or reversible/dissipative vocabularies.

data ProofStatus : Set where
  provedFinite : ProofStatus
  exactInterface : ProofStatus
  conditionalBridge : ProofStatus
  empiricalReceipt : ProofStatus
  openAnalyticTarget : ProofStatus

record CanonicalOwner : Set where
  constructor canonical-owner
  field
    concept : String
    moduleName : String
    status : ProofStatus
    parallelDefinitionAllowed : Bool
    parallelDefinitionAllowedIsFalse : parallelDefinitionAllowed ≡ false
open CanonicalOwner public

tritOwner : CanonicalOwner
tritOwner = canonical-owner
  "balanced ternary carrier"
  "DASHI.Algebra.Trit"
  provedFinite false refl

supportSignOwner : CanonicalOwner
supportSignOwner = canonical-owner
  "dependent support/sign factorisation"
  "DASHI.Algebra.TritSupportSignFactor"
  provedFinite false refl

multiscaleOwner : CanonicalOwner
multiscaleOwner = canonical-owner
  "multiscale carrier, residual, kernel, symmetry, and MDL step"
  "DASHI.Core.MultiscaleMDL"
  exactInterface false refl

ultrametricOwner : CanonicalOwner
ultrametricOwner = canonical-owner
  "369 prefix ultrametric"
  "DASHI.Geometry.SSP369Ultrametric"
  provedFinite false refl

mdlOwner : CanonicalOwner
mdlOwner = canonical-owner
  "MDL functional and Lyapunov contract"
  "DASHI.MDL.MDLLyapunov"
  exactInterface false refl

descentOwner : CanonicalOwner
descentOwner = canonical-owner
  "basin-local strict descent"
  "DASHI.Core.BasinFiniteDescent"
  exactInterface false refl

approximateNaturalityOwner : CanonicalOwner
approximateNaturalityOwner = canonical-owner
  "approximate multiscale kernel naturality"
  "DASHI.Core.ApproximateMultiscaleNaturality"
  exactInterface false refl

kernelSplitOwner : CanonicalOwner
kernelSplitOwner = canonical-owner
  "reversible evolution versus observation/dissipation"
  "DASHI.Core.ReversibleDissipativeKernelSplit"
  exactInterface false refl

codingTargetOwner : CanonicalOwner
codingTargetOwner = canonical-owner
  "source coding and rate-distortion targets"
  "DASHI.MDL.MultiscaleCodingTargets"
  openAnalyticTarget false refl

continuumTargetOwner : CanonicalOwner
continuumTargetOwner = canonical-owner
  "discrete-continuum, metric, and action targets"
  "DASHI.Physics.DiscreteContinuumKernelTargets"
  openAnalyticTarget false refl

canonicalOwners : List CanonicalOwner
canonicalOwners =
  tritOwner
  ∷ supportSignOwner
  ∷ multiscaleOwner
  ∷ ultrametricOwner
  ∷ mdlOwner
  ∷ descentOwner
  ∷ approximateNaturalityOwner
  ∷ kernelSplitOwner
  ∷ codingTargetOwner
  ∷ continuumTargetOwner
  ∷ []

record RepositoryClosureBoundary : Set where
  constructor repository-closure-boundary
  field
    canonicalOwnersRecorded : Bool
    canonicalOwnersRecordedIsTrue : canonicalOwnersRecorded ≡ true
    everythingCompileConfirmedHere : Bool
    everythingCompileConfirmedHereIsFalse : everythingCompileConfirmedHere ≡ false
    duplicateOwnersEliminatedAutomatically : Bool
    duplicateOwnersEliminatedAutomaticallyIsFalse :
      duplicateOwnersEliminatedAutomatically ≡ false
open RepositoryClosureBoundary public

canonicalRepositoryClosureBoundary : RepositoryClosureBoundary
canonicalRepositoryClosureBoundary =
  repository-closure-boundary true refl false refl false refl
