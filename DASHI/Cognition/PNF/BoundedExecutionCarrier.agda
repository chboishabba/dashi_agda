module DASHI.Cognition.PNF.BoundedExecutionCarrier where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; length)

open import DASHI.Cognition.PNF.ComplexityArithmetic
import DASHI.Cognition.PNF.BoundedProperNameEvidenceExecution as ProperName
import DASHI.Cognition.PNF.BoundedFactorCompositionExecution as Composition

------------------------------------------------------------------------
-- Generic bounded-execution carrier.
--
-- The proper-name and factor-composition lanes independently discovered the
-- same execution pattern: the semantic possibility carrier may be larger than
-- the materialised execution frontier.  A bounded representation therefore
-- carries the full observed possibility count, a retained-count budget and an
-- overflow/coverage receipt.  None of these execution facts is semantic
-- rejection or semantic authority.
------------------------------------------------------------------------

record BoundedEnumeration : Set where
  constructor boundedEnumeration
  field
    possibleCount : Nat
    retainedCount : Nat
    retainedLimit : Nat
    retainedWithinLimit : retainedCount ≤ᶜ retainedLimit

open BoundedEnumeration public

data EnumerationCoverage : Set where
  completeEnumeration boundedRepresentativeEnumeration : EnumerationCoverage

record BoundedExecutionCarrier (Candidate : Set) : Set where
  constructor boundedExecutionCarrier
  field
    enumeration : BoundedEnumeration
    retainedCandidates : List Candidate
    retainedCountMatches :
      length retainedCandidates ≡ retainedCount enumeration
    coverage : EnumerationCoverage

open BoundedExecutionCarrier public

record GenericOverflowReceipt : Set where
  constructor genericOverflowReceipt
  field
    overflowEnumeration : BoundedEnumeration
    overflowCoverage : EnumerationCoverage

open GenericOverflowReceipt public

data OverflowSemanticAuthority : Set where
  executionEvidenceOnly : OverflowSemanticAuthority

-- Deliberately constructorless.  Truncating the execution frontier cannot by
-- itself reject an omitted semantic possibility or license a semantic claim.
data OverflowSemanticPermission : OverflowSemanticAuthority → Set where

executionOverflowHasNoSemanticPermission :
  OverflowSemanticPermission executionEvidenceOnly → ⊥
executionOverflowHasNoSemanticPermission ()

------------------------------------------------------------------------
-- Optional measure/mass receipt.
--
-- Mass is deliberately abstract.  An application may instantiate it with
-- rationals, constructive reals, counts, log weights, or another exact carrier.
-- This layer only records the supplied split law; it does not manufacture a
-- probability measure or Born rule.
------------------------------------------------------------------------

record SplitMeasureReceipt
    (Mass : Set)
    (_⊕_ : Mass → Mass → Mass) : Set where
  constructor splitMeasureReceipt
  field
    totalMass retainedMass omittedMass : Mass
    retainedPlusOmittedIsTotal :
      retainedMass ⊕ omittedMass ≡ totalMass

open SplitMeasureReceipt public

record MeasuredBoundedExecutionCarrier
    (Candidate Mass : Set)
    (_⊕_ : Mass → Mass → Mass) : Set where
  constructor measuredBoundedExecutionCarrier
  field
    boundedCarrier : BoundedExecutionCarrier Candidate
    measureReceipt : SplitMeasureReceipt Mass _⊕_

open MeasuredBoundedExecutionCarrier public

------------------------------------------------------------------------
-- Existing runtime-specific bounded carriers embed into the generic shape.
-- This is intentionally a bridge, not a replacement of the existing theorem
-- names consumed by the SensibLaw correspondence.
------------------------------------------------------------------------

properNameEnumerationAsGeneric :
  ProperName.ProperNameTargetEnumeration → BoundedEnumeration
properNameEnumerationAsGeneric e =
  boundedEnumeration
    (ProperName.possibleTargetCount e)
    (ProperName.retainedTargetCount e)
    (ProperName.retainedTargetLimit e)
    (ProperName.retainedWithinLimit e)

compositionEnumerationAsGeneric :
  Composition.CompositionEnumeration → BoundedEnumeration
compositionEnumerationAsGeneric e =
  boundedEnumeration
    (Composition.possiblePairCount e)
    (Composition.retainedPairCount e)
    (Composition.retainedPairLimit e)
    (Composition.retainedWithinLimit e)

record BoundedExecutionAuthorityBoundary : Set where
  constructor boundedExecutionAuthorityBoundary
  field
    overflowCannotPromoteSemantics :
      OverflowSemanticPermission executionEvidenceOnly → ⊥

open BoundedExecutionAuthorityBoundary public

canonicalBoundedExecutionAuthorityBoundary : BoundedExecutionAuthorityBoundary
canonicalBoundedExecutionAuthorityBoundary =
  boundedExecutionAuthorityBoundary executionOverflowHasNoSemanticPermission
