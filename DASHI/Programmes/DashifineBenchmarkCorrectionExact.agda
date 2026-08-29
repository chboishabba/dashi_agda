module DASHI.Programmes.DashifineBenchmarkCorrectionExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- BIDI cut for dashifine benchmark claims.
--
-- A benchmark comparison is indexed by the actual task / split / observable.
-- It may certify a task-specific ordering.  Universal learning or projection
-- claims require the corresponding family-indexed receipt and cannot be
-- obtained by dropping the task index from one successful benchmark.
------------------------------------------------------------------------

record TaskIndexedComparison
    (Task Model Score : Set) : Set₁ where
  constructor taskIndexedComparison
  field
    score : Task → Model → Score
    Better : Score → Score → Set

open TaskIndexedComparison public

TaskDominates :
  ∀ {Task Model Score : Set} →
  TaskIndexedComparison Task Model Score →
  Task → Model → Model → Set
TaskDominates comparison task left right =
  Better comparison
    (score comparison task left)
    (score comparison task right)

record BenchmarkReceipt
    {Task Model Score : Set}
    (comparison : TaskIndexedComparison Task Model Score)
    (task : Task)
    (left right : Model) : Set where
  constructor benchmarkReceipt
  field
    taskDominance : TaskDominates comparison task left right

open BenchmarkReceipt public

record FamilyDominanceReceipt
    {Task Model Score : Set}
    (comparison : TaskIndexedComparison Task Model Score)
    (left right : Model) : Set where
  constructor familyDominanceReceipt
  field
    allTasks :
      (task : Task) → TaskDominates comparison task left right

open FamilyDominanceReceipt public

familyReceiptSpecializesToBenchmark :
  ∀ {Task Model Score : Set}
    {comparison : TaskIndexedComparison Task Model Score}
    {left right : Model} →
  FamilyDominanceReceipt comparison left right →
  (task : Task) →
  BenchmarkReceipt comparison task left right
familyReceiptSpecializesToBenchmark receipt task =
  benchmarkReceipt (allTasks receipt task)

record DashifineBenchmarkCorrectionBoundary : Set where
  constructor dashifineBenchmarkCorrectionBoundary
  field
    oneTaskDominanceIsUniversalLearning : Bool
    oneTaskDominanceIsUniversalLearningIsFalse :
      oneTaskDominanceIsUniversalLearning ≡ false

    placeholderCLISmokeIsNumericalBenchmarkReceipt : Bool
    placeholderCLISmokeIsNumericalBenchmarkReceiptIsFalse :
      placeholderCLISmokeIsNumericalBenchmarkReceipt ≡ false

    heldOutFamilyReceiptMaySupportFamilyClaim : Bool
    heldOutFamilyReceiptMaySupportFamilyClaimIsTrue :
      heldOutFamilyReceiptMaySupportFamilyClaim ≡ true

canonicalDashifineBenchmarkCorrectionBoundary :
  DashifineBenchmarkCorrectionBoundary
canonicalDashifineBenchmarkCorrectionBoundary =
  dashifineBenchmarkCorrectionBoundary
    false refl
    false refl
    true refl
