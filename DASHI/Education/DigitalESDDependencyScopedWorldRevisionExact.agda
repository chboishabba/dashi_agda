module DASHI.Education.DigitalESDDependencyScopedWorldRevisionExact where

------------------------------------------------------------------------
-- ESD world revision over the canonical reverse-dependency closure.
-- Reuses DASHI.Core.AffectedDependencyClosureExact and the existing
-- AliceBrownDependencyDerivedInvalidationBidiExact owner. No source
-- observations, participant decisions or empirical timeline are invented.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AffectedDependencyClosureExact as Closure
import DASHI.Biology.AliceBrownDependencyDerivedInvalidationBidiExact as Alice
import DASHI.Education.DigitalESDOpenAxisStudyPartWorldExact as World

-- XT00: an affected address cannot carry an old candidate judgement
-- forward silently. It is either explicitly reopened, or paid again with
-- a genuine reviewed full-text source observation at that exact address.
data AffectedPartAxisDisposition
  (scope : World.StudyWorldScope)
  (after : World.AccountedStudyWorld scope)
  (s : World.Study scope)
  (p : World.Part scope s)
  (axis : World.Axis scope) : Set₁ where
  reopenedForReview :
    (reviewWork : String) →
    World.accounting after s p axis ≡ World.notYetAssessed reviewWork →
    AffectedPartAxisDisposition scope after s p axis
  revalidatedAgainstSource :
    (reviewed : World.ReviewedPartAxisEvidence scope s p axis) →
    World.accounting after s p axis ≡ World.directReviewed reviewed →
    AffectedPartAxisDisposition scope after s p axis

-- XT01: truth maintenance is scoped to an actual source-owned dependency
-- relation and its reflexive/transitive reachability. Unreachable addresses
-- retain the identical typed account. Reachable addresses explicitly reopen
-- or furnish the reviewed evidence witness needed to revalidate them.
record DependencyGovernedResearchWorldRevision
  (scope : World.StudyWorldScope)
  (Artifact : Set)
  (Depends : Artifact → Artifact → Set)
  (before after : World.AccountedStudyWorld scope) : Set₂ where
  constructor dependency-governed-world-revision
  field
    changed : Artifact

    addressOwner :
      (s : World.Study scope) →
      (p : World.Part scope s) →
      (axis : World.Axis scope) → Artifact

    unrelatedAddressesRetained :
      (s : World.Study scope) →
      (p : World.Part scope s) →
      (axis : World.Axis scope) →
      (Closure.AffectedClosure Depends changed (addressOwner s p axis) → ⊥) →
      World.accounting after s p axis ≡ World.accounting before s p axis

    dependentAddressesHandled :
      (s : World.Study scope) →
      (p : World.Part scope s) →
      (axis : World.Axis scope) →
      Closure.AffectedClosure Depends changed (addressOwner s p axis) →
      AffectedPartAxisDisposition scope after s p axis

open DependencyGovernedResearchWorldRevision public

-- XT02: caller cannot claim an unrelated axis was changed by the update
-- if it has a proof of no dependency path; derive equality instead.
unaffectedAddressStillHasSameAssessment :
  (scope : World.StudyWorldScope) →
  (Artifact : Set) →
  (Depends : Artifact → Artifact → Set) →
  (before after : World.AccountedStudyWorld scope) →
  (revision : DependencyGovernedResearchWorldRevision
    scope Artifact Depends before after) →
  (s : World.Study scope) →
  (p : World.Part scope s) →
  (axis : World.Axis scope) →
  (Closure.AffectedClosure Depends
    (changed revision) (addressOwner revision s p axis) → ⊥) →
  World.accounting after s p axis ≡ World.accounting before s p axis
unaffectedAddressStillHasSameAssessment
  scope Artifact Depends before after revision s p axis noPath =
  unrelatedAddressesRetained revision s p axis noPath

-- XT03: explicit Alice dependency-derived example retained as a
-- methodological donor, NOT proof of an actual ESD study-world revision.
aliceParentObserverUnaffectedExample =
  Alice.aliceParentObserverCandidateStillUnaffected

-- XT04: correlation or source similarity cannot construct reachability.
-- The only actual way into the affected field is the proof-bearing
-- AffectedClosure of the canonical owner.
data SimilarityCreatesDependencyPath : Set where
similarityIsNotDependencyEvidence : SimilarityCreatesDependencyPath → ⊥
similarityIsNotDependencyEvidence ()
