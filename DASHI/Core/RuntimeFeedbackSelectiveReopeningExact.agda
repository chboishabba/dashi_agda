module DASHI.Core.RuntimeFeedbackSelectiveReopeningExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AffectedDependencyClosureExact as Closure

------------------------------------------------------------------------
-- RUNTIME FEEDBACK -> EXACT SELECTIVE REOPENING
--
-- A changed observation/artifact does not invalidate everything.  Reopening is
-- justified by a proof-bearing dependency path.  Retention is only justified
-- when absence of such a path is itself available as evidence.
------------------------------------------------------------------------

record ChangedArtifact {Artifact : Set} : Set₁ where
  constructor changed-artifact
  field
    artifact : Artifact
    observationReference : String
    changeReference : String

open ChangedArtifact public

record ReopenTarget
    {Artifact : Set}
    (Depends : Artifact → Artifact → Set)
    (changed : Artifact) : Set₁ where
  constructor reopen-target
  field
    target : Artifact
    obligation : Closure.ReopeningObligation Depends changed target
    reopeningReference : String

open ReopenTarget public

record RetainTarget
    {Artifact : Set}
    (Depends : Artifact → Artifact → Set)
    (changed : Artifact) : Set₁ where
  constructor retain-target
  field
    target : Artifact
    noAffectedPath : Closure.AffectedClosure Depends changed target → ⊥
    retentionReference : String

open RetainTarget public

record RuntimeReopeningPlan {Artifact : Set} (Depends : Artifact → Artifact → Set) : Set₂ where
  constructor runtime-reopening-plan
  field
    changed : Artifact
    reopen : Artifact → Set
    retain : Artifact → Set
    reopenSound :
      ∀ target →
      reopen target →
      Closure.ReopeningObligation Depends changed target
    retainSound :
      ∀ target →
      retain target →
      Closure.AffectedClosure Depends changed target → ⊥
    planReference : String

open RuntimeReopeningPlan public

record RuntimeSelectiveReopeningBoundary : Set where
  constructor runtime-selective-reopening-boundary
  field
    changedArtifactInvalidatesEverything : Bool
    changedArtifactInvalidatesEverythingIsFalse :
      changedArtifactInvalidatesEverything ≡ false

    directDependentsAreAlwaysWholeAffectedRegion : Bool
    directDependentsAreAlwaysWholeAffectedRegionIsFalse :
      directDependentsAreAlwaysWholeAffectedRegion ≡ false

    correlationMayReplaceDependencyProof : Bool
    correlationMayReplaceDependencyProofIsFalse :
      correlationMayReplaceDependencyProof ≡ false

    retentionNeedsNoDependencyPathEvidence : Bool
    retentionNeedsNoDependencyPathEvidenceIsTrue :
      retentionNeedsNoDependencyPathEvidence ≡ true

canonicalRuntimeSelectiveReopeningBoundary : RuntimeSelectiveReopeningBoundary
canonicalRuntimeSelectiveReopeningBoundary =
  runtime-selective-reopening-boundary
    false refl
    false refl
    false refl
    true refl
