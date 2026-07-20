module DASHI.Philosophy.CulturalProvenanceAdapter where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Culture.CulturalProvenanceBoundaryCore as Cultural

------------------------------------------------------------------------
-- Philosophy applications reuse the canonical cultural provenance owner.
-- Inspiration and representation remain distinct promotions.

record PhilosophyCulturalAdapter : Set where
  constructor mkPhilosophyCulturalAdapter
  field
    provenanceBoundary : Cultural.CulturalProvenanceBoundary
    namedSourceTradition : String
    exactSourceOrSpeaker : String
    localContext : String
    adaptationMadeByDASHI : String
    inspiredBy : Bool
    representsTradition : Bool
    authorityPresent : Bool
    explicitNonRepresentationClaim : Bool

open PhilosophyCulturalAdapter public

canonicalPhilosophyCulturalAdapter : PhilosophyCulturalAdapter
canonicalPhilosophyCulturalAdapter =
  mkPhilosophyCulturalAdapter
    Cultural.canonicalCulturalProvenanceBoundary
    "named source tradition required per application"
    "exact source or speaker required per application"
    "local context required per application"
    "formal relational analogy only"
    true
    false
    false
    true

canonicalInspiredDoesNotRepresent :
  representsTradition canonicalPhilosophyCulturalAdapter ≡ false
canonicalInspiredDoesNotRepresent = refl

record CulturalApplicationPromotion : Set where
  field
    adapter : PhilosophyCulturalAdapter
    sourceAuthorityReceipt : Set
    communityOrSpeakerAuthorityReceipt : Set
    adaptationBoundaryReceipt : Set
    representationPromoted : Bool

open CulturalApplicationPromotion public
