module DASHI.Cognition.PNF.BoundedExecutionAdapters where

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using (List; length)

import DASHI.Cognition.PNF.BoundedExecutionCarrier as Generic
import DASHI.Cognition.PNF.BoundedFactorCompositionExecution as Composition
import DASHI.Cognition.PNF.BoundedProperNameEvidenceExecution as ProperName

properNameCoverageAsGeneric :
  ProperName.ProperNameEnumerationCoverage → Generic.EnumerationCoverage
properNameCoverageAsGeneric ProperName.completeEnumeration =
  Generic.completeEnumeration
properNameCoverageAsGeneric ProperName.boundedRepresentativeEnumeration =
  Generic.boundedRepresentativeEnumeration

compositionCoverageAsGeneric :
  Composition.CompositionOverflowState → Generic.EnumerationCoverage
compositionCoverageAsGeneric Composition.completeWithinBudget =
  Generic.completeEnumeration
compositionCoverageAsGeneric Composition.overflowObserved =
  Generic.boundedRepresentativeEnumeration

properNameCarrierAsGeneric :
  ∀ {Candidate : Set} →
  (enumeration : ProperName.ProperNameTargetEnumeration) →
  (retained : List Candidate) →
  length retained ≡ ProperName.retainedTargetCount enumeration →
  ProperName.ProperNameEnumerationCoverage →
  Generic.BoundedExecutionCarrier Candidate
properNameCarrierAsGeneric enumeration retained countMatches coverage =
  Generic.boundedExecutionCarrier
    (Generic.properNameEnumerationAsGeneric enumeration)
    retained
    countMatches
    (properNameCoverageAsGeneric coverage)

compositionCarrierAsGeneric :
  ∀ {Candidate : Set} →
  (enumeration : Composition.CompositionEnumeration) →
  (retained : List Candidate) →
  length retained ≡ Composition.retainedPairCount enumeration →
  Composition.CompositionOverflowState →
  Generic.BoundedExecutionCarrier Candidate
compositionCarrierAsGeneric enumeration retained countMatches overflow =
  Generic.boundedExecutionCarrier
    (Generic.compositionEnumerationAsGeneric enumeration)
    retained
    countMatches
    (compositionCoverageAsGeneric overflow)
