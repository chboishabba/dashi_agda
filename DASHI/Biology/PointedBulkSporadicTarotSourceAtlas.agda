module DASHI.Biology.PointedBulkSporadicTarotSourceAtlas where

open import DASHI.Core.Prelude

import DASHI.Biology.ConsciousAccessRound4SourceAtlas as Source
import DASHI.Biology.ConsciousAccessRound5CompletionSourceAtlas as Existing

------------------------------------------------------------------------
-- Bounded sources for the sporadic inventory, Mathieu-degree bridge,
-- representation decomposition and moonshine promotion boundary.
------------------------------------------------------------------------

atlasFiniteGroupsSource : Source.SourceRecord
atlasFiniteGroupsSource =
  Source.sourceRecord
    "J. H. Conway; R. T. Curtis; S. P. Norton; R. A. Parker; R. A. Wilson"
    "Atlas of Finite Groups: Maximal Subgroups and Ordinary Characters for Simple Groups"
    "Oxford University Press"
    1985
    "No DOI assigned; ISBN 0-19-853199-0"
    "Supports the complete twenty-six-group sporadic inventory, standard names, Conway-group count and family classification used by the mathematical validity ledger."
    "The ATLAS inventory does not define a twenty-two-card Tarot correspondence or identify a synthetic Co4 card with a sporadic simple group."

curtisMathieuSource : Source.SourceRecord
curtisMathieuSource =
  Source.sourceRecord
    "R. T. Curtis"
    "Natural Constructions of the Mathieu Groups"
    "Mathematical Proceedings of the Cambridge Philosophical Society 106(3), 423-429"
    1989
    "10.1017/S0305004100068158"
    "Supports the natural permutation degrees and the distinction between Mathieu constructions, designs and later exceptional-group relationships."
    "The source does not make every finite-geometry-to-Monster arrow a canonical implication or supply a Tarot projection."

fultonHarrisRepresentationSource : Source.SourceRecord
fultonHarrisRepresentationSource =
  Existing.fultonHarrisRepresentationSource

borcherdsMoonshineSource : Source.SourceRecord
borcherdsMoonshineSource =
  Existing.borcherdsMoonshineProofSource

canonicalPointedBulkSporadicTarotSources : List Source.SourceRecord
canonicalPointedBulkSporadicTarotSources =
  atlasFiniteGroupsSource
  ∷ curtisMathieuSource
  ∷ fultonHarrisRepresentationSource
  ∷ borcherdsMoonshineSource
  ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ xs) = suc (listCount xs)

canonicalSourceCount : Nat
canonicalSourceCount = listCount canonicalPointedBulkSporadicTarotSources

canonicalSourceCountIsFour : canonicalSourceCount ≡ 4
canonicalSourceCountIsFour = refl
