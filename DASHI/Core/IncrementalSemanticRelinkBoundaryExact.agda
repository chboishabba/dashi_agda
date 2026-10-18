module DASHI.Core.IncrementalSemanticRelinkBoundaryExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- INCREMENTAL SEMANTIC RELINK BOUNDARY
--
-- A local source change does not authorize deleting/rebuilding the entire
-- repository reference graph. Incremental consumers should invalidate changed
-- declarations and the scopes/importers whose name-resolution evidence can be
-- affected, leaving unrelated semantic edges intact.
------------------------------------------------------------------------

data RelinkScope : Set where
  changedDeclarationScope : RelinkScope
  affectedNameResolutionScope : RelinkScope
  wholeCorpusScope : RelinkScope

data RelinkAdmission : Set where
  relinkAdmitted : RelinkAdmission
  relinkRejected : RelinkAdmission

relinkAdmission : RelinkScope → RelinkAdmission
relinkAdmission changedDeclarationScope = relinkAdmitted
relinkAdmission affectedNameResolutionScope = relinkAdmitted
relinkAdmission wholeCorpusScope = relinkRejected

wholeCorpusRelinkNotDefault :
  relinkAdmission wholeCorpusScope ≡ relinkRejected
wholeCorpusRelinkNotDefault = refl

record IncrementalSemanticRelinkBoundary : Set where
  constructor incrementalSemanticRelinkBoundary
  field
    oneChangedFileImpliesGlobalRelink : Bool
    oneChangedFileImpliesGlobalRelinkIsFalse :
      oneChangedFileImpliesGlobalRelink ≡ false

    unrelatedEdgesMayBeInvalidatedWithoutEvidence : Bool
    unrelatedEdgesMayBeInvalidatedWithoutEvidenceIsFalse :
      unrelatedEdgesMayBeInvalidatedWithoutEvidence ≡ false

    affectedScopesMayBeRecomputed : Bool
    affectedScopesMayBeRecomputedIsTrue :
      affectedScopesMayBeRecomputed ≡ true

canonicalIncrementalSemanticRelinkBoundary :
  IncrementalSemanticRelinkBoundary
canonicalIncrementalSemanticRelinkBoundary =
  incrementalSemanticRelinkBoundary
    false refl
    false refl
    true refl
