module DASHI.Core.SelectorDiscriminationSearchExact where

------------------------------------------------------------------------
-- SELECTOR DISCRIMINATION SEARCH
--
-- Coverage alone is cheap: a public observer can see enormous numbers of
-- people.  Investigative value therefore requires three independent receipts:
--   coverage, discrimination, and provenance.
--
-- This module does not infer probability, causality, targeting, or adversary.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.CommonSelectorVisibilityHyperfabricExact as Visibility

------------------------------------------------------------------------
-- Search coordinates.
------------------------------------------------------------------------

data SupportGrade : Set where
  sourceBacked
  partiallySourceBacked
  unlocated
  knownAbsent
  : SupportGrade

data DiscriminationGrade : Set where
  extremelyCoarse
  coarse
  intermediate
  narrow
  rosterSpecific
  unresolvedDiscrimination
  : DiscriminationGrade

record SelectorSearchCandidate : Set₁ where
  constructor selector-search-candidate
  field
    candidateSelector : Visibility.SelectorClass
    support : SupportGrade
    discrimination : DiscriminationGrade
    acquisitionCost : Nat
    coverageReference : String
    discriminationReference : String
    provenanceReference : String

open SelectorSearchCandidate public

------------------------------------------------------------------------
-- A selector is admissible for explanatory search only after coverage and
-- discrimination are independently justified.  Merely being able to see the
-- roster is not enough.
------------------------------------------------------------------------

record CoversDeclaredRoster (candidate : SelectorSearchCandidate) : Set where
  constructor covers-declared-roster
  field
    coverageReceipt : String

record DiscriminatesDeclaredRoster (candidate : SelectorSearchCandidate) : Set where
  constructor discriminates-declared-roster
  field
    discriminationReceipt : String

record SourceBackedCandidate (candidate : SelectorSearchCandidate) : Set where
  constructor source-backed-candidate
  field
    provenanceReceipt : String

record AdmissibleSelectorExplanation (candidate : SelectorSearchCandidate) : Set where
  constructor admissible-selector-explanation
  field
    covers : CoversDeclaredRoster candidate
    discriminates : DiscriminatesDeclaredRoster candidate
    sourceBacked : SourceBackedCandidate candidate

open AdmissibleSelectorExplanation public

------------------------------------------------------------------------
-- Cost is optimized only AFTER admissibility.  This mirrors DASHI's existing
-- least-coupled / least-cost proof-search discipline.
------------------------------------------------------------------------

record LeastCostAdmissibleSelector
    (Declared : SelectorSearchCandidate → Set) : Set₁ where
  constructor least-cost-admissible-selector
  field
    chosen : SelectorSearchCandidate
    chosenDeclared : Declared chosen
    chosenAdmissible : AdmissibleSelectorExplanation chosen
    minimal :
      (alternative : SelectorSearchCandidate) →
      Declared alternative →
      AdmissibleSelectorExplanation alternative →
      acquisitionCost chosen ≤ acquisitionCost alternative
    minimalityReference : String

open LeastCostAdmissibleSelector public

------------------------------------------------------------------------
-- Frontier object: when coverage exists but discrimination or provenance does
-- not, emit exactly the missing acquisition rather than promoting the selector.
------------------------------------------------------------------------

data MissingSelectorReceipt : Set where
  missingCoverage
  missingDiscrimination
  missingProvenance
  : MissingSelectorReceipt

record SelectorAcquisitionFrontier : Set₁ where
  constructor selector-acquisition-frontier
  field
    candidate : SelectorSearchCandidate
    missing : MissingSelectorReceipt
    requestedEvidence : String
    consumerReference : String

open SelectorAcquisitionFrontier public

record SelectorDiscriminationBoundary : Set where
  constructor selector-discrimination-boundary
  field
    coverageAloneExplainsSelection : Bool
    coverageAloneExplainsSelectionIsFalse :
      coverageAloneExplainsSelection ≡ false

    discriminationWithoutProvenanceIsEnough : Bool
    discriminationWithoutProvenanceIsEnoughIsFalse :
      discriminationWithoutProvenanceIsEnough ≡ false

    lowAcquisitionCostOverridesAdmissibility : Bool
    lowAcquisitionCostOverridesAdmissibilityIsFalse :
      lowAcquisitionCostOverridesAdmissibility ≡ false

    publicSearchabilityIsRosterSpecific : Bool
    publicSearchabilityIsRosterSpecificIsFalse :
      publicSearchabilityIsRosterSpecific ≡ false

    sourceBackedCommonObserverImpliesAdversary : Bool
    sourceBackedCommonObserverImpliesAdversaryIsFalse :
      sourceBackedCommonObserverImpliesAdversary ≡ false

canonicalSelectorDiscriminationBoundary : SelectorDiscriminationBoundary
canonicalSelectorDiscriminationBoundary =
  selector-discrimination-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
