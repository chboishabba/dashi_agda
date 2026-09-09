module DASHI.Law.SensibLawCullenSourceGroundedReviewedUnitsExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Source-grounded Cullen review subset.
--
-- Rust source compiles only five bounded review units supported directly by the
-- retained Cullen judgment:
--   Robinson @ body 89  -> relied-on / rule
--   Robinson @ body 91  -> relied-on / analogy
--   Modbury  @ body 93  -> distinguished / distinction
--   Modbury  @ body 148 -> distinguished / distinction
--   Robinson @ body 148 -> relied-on / rule
--
-- The resulting ReasoningGraphDelta is candidate-only.  The live residual is
-- narrowed but deliberately remains Open/Continue.  No source text here is
-- used to claim that the residual is fully paid or that the cited authorities
-- have become binding/current merely through this review.
------------------------------------------------------------------------

rustRepository : String
rustRepository = "chboishabba/slr"

rustBranch : String
rustBranch = "agent/governed-online-r6-v2"

observedReviewUnitHead : String
observedReviewUnitHead = "8f8efafadea86f0b56246917e89c8b916deb5289"

sourceGroundedReviewSourceHead : String
sourceGroundedReviewSourceHead = "869651520bc01361629d400b03a6d913c2c4ce3e"

record CullenSourceGroundedReviewedUnitsBoundary : Set where
  constructor cullenSourceGroundedReviewedUnitsBoundary
  field
    selectedReviewUnitCount : Nat
    selectedReviewUnitCountIs5 : selectedReviewUnitCount ≡ 5

    reviewedReasoningEdgeCount : Nat
    reviewedReasoningEdgeCountIs5 : reviewedReasoningEdgeCount ≡ 5

    distinguishedEdgeCount : Nat
    distinguishedEdgeCountIs2 : distinguishedEdgeCount ≡ 2

    allOccurrenceLocatorsPreservedInReviewReceipts : Bool
    allOccurrenceLocatorsPreservedInReviewReceiptsIsTrue :
      allOccurrenceLocatorsPreservedInReviewReceipts ≡ true

    reasoningDeltaCandidateOnly : Bool
    reasoningDeltaCandidateOnlyIsTrue : reasoningDeltaCandidateOnly ≡ true

    frontierNarrowed : Bool
    frontierNarrowedIsTrue : frontierNarrowed ≡ true

    frontierStillOpen : Bool
    frontierStillOpenIsTrue : frontierStillOpen ≡ true

    terminationContinue : Bool
    terminationContinueIsTrue : terminationContinue ≡ true

    sourceGroundedFixtureLocallyObserved : Bool
    sourceGroundedFixtureLocallyObservedIsFalse :
      sourceGroundedFixtureLocallyObserved ≡ false

canonicalCullenSourceGroundedReviewedUnitsBoundary :
  CullenSourceGroundedReviewedUnitsBoundary
canonicalCullenSourceGroundedReviewedUnitsBoundary =
  cullenSourceGroundedReviewedUnitsBoundary
    5 refl
    5 refl
    2 refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ReviewedSubsetAutomaticallyPaysResidual : Set where
data ReviewedSubsetAutomaticallyCurrentAuthority : Set where
data NarrowedFrontierAutomaticallyClosed : Set where

reviewedSubsetDoesNotAutomaticallyPayResidual :
  ReviewedSubsetAutomaticallyPaysResidual → ⊥
reviewedSubsetDoesNotAutomaticallyPayResidual ()

reviewedSubsetDoesNotAutomaticallyBecomeCurrentAuthority :
  ReviewedSubsetAutomaticallyCurrentAuthority → ⊥
reviewedSubsetDoesNotAutomaticallyBecomeCurrentAuthority ()

narrowedFrontierDoesNotAutomaticallyClose :
  NarrowedFrontierAutomaticallyClosed → ⊥
narrowedFrontierDoesNotAutomaticallyClose ()
