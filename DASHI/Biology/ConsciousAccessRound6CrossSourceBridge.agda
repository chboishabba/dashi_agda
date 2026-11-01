module DASHI.Biology.ConsciousAccessRound6CrossSourceBridge where

open import DASHI.Core.Prelude

import DASHI.Biology.ConsciousAccessRound4SourceAtlas as R4
import DASHI.Biology.ConsciousAccessRound5SourceAtlas as R5
import DASHI.Biology.ConsciousAccessRound5ExtendedSourceAtlas as R5X

------------------------------------------------------------------------
-- No new empirical source is invented for the cross-pollination theorem.
-- The bridge explicitly reuses the already attributed source records whose
-- mathematical roles are composed by Round Six.

canonicalRound6CrossSources : List R4.SourceRecord
canonicalRound6CrossSources =
  R5.turingMorphogenesisSource
  ∷ R5.chungSpectralGraphSource
  ∷ R5X.artinBraidSource
  ∷ R5.ruttZhouyiSource
  ∷ []

canonicalRound6CrossSourceCount : Nat
canonicalRound6CrossSourceCount =
  R4.listCount canonicalRound6CrossSources

canonicalRound6CrossSourceCountIsFour :
  canonicalRound6CrossSourceCount ≡ 4
canonicalRound6CrossSourceCountIsFour = refl

record CrossSourceBoundary : Set where
  constructor crossSourceBoundary
  field
    sourceConjunctionProvesSharedMechanism : Bool
    sourceConjunctionProvesSharedMechanismIsFalse :
      sourceConjunctionProvesSharedMechanism ≡ false

    sourceReuseCreatesNewEmpiricalEvidence : Bool
    sourceReuseCreatesNewEmpiricalEvidenceIsFalse :
      sourceReuseCreatesNewEmpiricalEvidence ≡ false

canonicalCrossSourceBoundary : CrossSourceBoundary
canonicalCrossSourceBoundary =
  crossSourceBoundary false refl false refl
