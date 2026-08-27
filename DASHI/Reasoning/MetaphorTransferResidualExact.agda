module DASHI.Reasoning.MetaphorTransferResidualExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- METAPHOR / STRUCTURAL-TRANSFER RESIDUALS
--
-- A lossy structural transfer can fail in at least two importantly different
-- ways:
--
--   * MISS residual: target structure needed by a consumer is not carried;
--   * SPURIOUS residual: source structure is imported although the target does
--     not support the corresponding claim.
--
-- This is an original DASHI formalisation.  Stuart & Wilkenfeld (2022), DOI
-- 10.1007/s13194-022-00479-5, motivate context- and consequence-relative
-- metaphor evaluation.  Nusrat Fatima (2026), DOI 10.46809/jcsll.v7i2.430,
-- motivates explicit methodological withdrawal when an imported structural
-- vocabulary no longer fits the target.  Neither source states this record.
------------------------------------------------------------------------

data ResidualKind : Set where
  missingTargetStructure spuriousSourceTransfer : ResidualKind

record TransferResidualProfile : Set₁ where
  field
    SourceFeature : Set
    TargetFeature : Set
    ConsumerRequirement : Set

    sourceFeatureTransferred : SourceFeature → Bool
    targetFeatureAvailable : TargetFeature → Bool
    consumerRequires : ConsumerRequirement → TargetFeature

    residualKind : ResidualKind
    residualReading : String

open TransferResidualProfile public

------------------------------------------------------------------------
-- Exact finite witnesses separating under-transfer from over-transfer.
------------------------------------------------------------------------

data ToySourceFeature : Set where
  multiplicity relation recurrence : ToySourceFeature

data ToyTargetFeature : Set where
  severalItems reciprocalRelation recoverableReturn : ToyTargetFeature

data ToyRequirement : Set where
  askReciprocity askRecoverability : ToyRequirement

sourceTransferredForMiss : ToySourceFeature → Bool
sourceTransferredForMiss multiplicity = true
sourceTransferredForMiss relation = false
sourceTransferredForMiss recurrence = false

targetAvailableForMiss : ToyTargetFeature → Bool
targetAvailableForMiss severalItems = true
targetAvailableForMiss reciprocalRelation = true
targetAvailableForMiss recoverableReturn = false

requiresToy : ToyRequirement → ToyTargetFeature
requiresToy askReciprocity = reciprocalRelation
requiresToy askRecoverability = recoverableReturn

missingReciprocityProfile : TransferResidualProfile
missingReciprocityProfile =
  record
    { SourceFeature = ToySourceFeature
    ; TargetFeature = ToyTargetFeature
    ; ConsumerRequirement = ToyRequirement
    ; sourceFeatureTransferred = sourceTransferredForMiss
    ; targetFeatureAvailable = targetAvailableForMiss
    ; consumerRequires = requiresToy
    ; residualKind = missingTargetStructure
    ; residualReading =
        "The compressed frame carries multiplicity but omits a target relation required by the consumer: this is under-transfer, not false positive structure."
    }

sourceTransferredForSpurious : ToySourceFeature → Bool
sourceTransferredForSpurious multiplicity = true
sourceTransferredForSpurious relation = true
sourceTransferredForSpurious recurrence = true

targetAvailableForSpurious : ToyTargetFeature → Bool
targetAvailableForSpurious severalItems = true
targetAvailableForSpurious reciprocalRelation = true
targetAvailableForSpurious recoverableReturn = false

spuriousRecoverabilityProfile : TransferResidualProfile
spuriousRecoverabilityProfile =
  record
    { SourceFeature = ToySourceFeature
    ; TargetFeature = ToyTargetFeature
    ; ConsumerRequirement = ToyRequirement
    ; sourceFeatureTransferred = sourceTransferredForSpurious
    ; targetFeatureAvailable = targetAvailableForSpurious
    ; consumerRequires = requiresToy
    ; residualKind = spuriousSourceTransfer
    ; residualReading =
        "The frame imports a recurrence/recoverability expectation even though the target does not support recoverable return: this is over-transfer rather than mere omission."
    }

missingAndSpuriousAreDistinct :
  missingTargetStructure ≡ spuriousSourceTransfer → Bool
missingAndSpuriousAreDistinct ()

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record TransferResidualBoundary : Set where
  constructor transferResidualBoundary
  field
    everyBadMetaphorFailsInTheSameWay : Bool
    everyBadMetaphorFailsInTheSameWayIsFalse :
      everyBadMetaphorFailsInTheSameWay ≡ false

    omissionAndSpuriousInferenceAreIdentical : Bool
    omissionAndSpuriousInferenceAreIdenticalIsFalse :
      omissionAndSpuriousInferenceAreIdentical ≡ false

    contextLocalFitnessImpliesGlobalPredicateTransfer : Bool
    contextLocalFitnessImpliesGlobalPredicateTransferIsFalse :
      contextLocalFitnessImpliesGlobalPredicateTransfer ≡ false

    failedTransferCanRequireWithdrawalRatherThanRepair : Bool
    failedTransferCanRequireWithdrawalRatherThanRepairIsTrue :
      failedTransferCanRequireWithdrawalRatherThanRepair ≡ true

canonicalTransferResidualBoundary : TransferResidualBoundary
canonicalTransferResidualBoundary =
  transferResidualBoundary
    false refl
    false refl
    false refl
    true refl
