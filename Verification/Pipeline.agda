module Verification.Pipeline where

open import Verification.Prelude
open import Verification.SourceHash
open import Verification.ExecutionReview
open import Verification.ZK
open import Verification.CostProfile
open import Verification.BinaryPatching
open import Verification.LMFDB

record VerificationPipeline : Set₁ where
  field
    integrity : SourceIntegrity
    review    : ExecutionReview
    zk        : ZKCorrectness
    cost      : CostWithin
    patching  : PatchCorrect
    lmfdb     : LMFDBVerified
