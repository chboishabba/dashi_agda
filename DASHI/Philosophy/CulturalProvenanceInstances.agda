module DASHI.Philosophy.CulturalProvenanceInstances where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Culture.CulturalProvenanceBoundaryCore as Cultural
import DASHI.Philosophy.CulturalProvenanceAdapter as Adapter

------------------------------------------------------------------------
-- Candidate provenance rows. These identify sources and DASHI adaptations;
-- they do not claim community authority or representation.

patternMindRow : Cultural.ProvenanceRow
patternMindRow =
  Cultural.mkProvenanceRow
    "Tyson Yunkaporta, Sand Talk"
    Cultural.namedAuthorProvenance
    "pattern-thinking and situated relational interpretation used as philosophical inspiration"
    "DASHI does not represent Aboriginal knowledge systems, community authority, or the full argument of the source"
    false
    false

reciprocityRow : Cultural.ProvenanceRow
reciprocityRow =
  Cultural.mkProvenanceRow
    "Robin Wall Kimmerer, Braiding Sweetgrass"
    Cultural.namedAuthorProvenance
    "reciprocity and responsibility toward living systems used as philosophical inspiration"
    "formal analogy does not substitute for Potawatomi knowledge, living practice, or source-specific context"
    false
    false

yarningMethodRow : Cultural.ProvenanceRow
yarningMethodRow =
  Cultural.mkProvenanceRow
    "Indigenous yarning methodologies — exact local source required per application"
    Cultural.comparativeResearchProvenance
    "dialogical process and relationship-building treated as a candidate methodological analogy"
    "yarning is not one universal method and cannot be detached from community, purpose, authority, and place"
    false
    false

maoriPlantTeachingRow : Cultural.ProvenanceRow
maoriPlantTeachingRow =
  Cultural.mkProvenanceRow
    "User-supplied Māori plant-teaching example — exact speaker, iwi, place, plant identification, and permission unresolved"
    Cultural.placePracticeProvenance
    "local sensory teaching used only as a candidate example of pattern-preserving participation"
    "no Māori representation, botanical verification, cultural authority, or generalisation is promoted"
    false
    false

relationalLawRow : Cultural.ProvenanceRow
relationalLawRow =
  Cultural.mkProvenanceRow
    "Indigenous relational-law language — named nation and authoritative source required"
    Cultural.formalAnalogyProvenance
    "used only to motivate responsibility, non-domination, and relation-sensitive governance"
    "no pan-Indigenous synthesis, legal authority, or replacement of living law is claimed"
    false
    false

canonicalPhilosophyProvenanceRows : List Cultural.ProvenanceRow
canonicalPhilosophyProvenanceRows =
  patternMindRow
  ∷ reciprocityRow
  ∷ yarningMethodRow
  ∷ maoriPlantTeachingRow
  ∷ relationalLawRow
  ∷ []

record ProvenanceInstanceBoundary : Set where
  constructor provenanceInstanceBoundary
  field
    exactSourceRequired : Bool
    localContextRequired : Bool
    permissionOrAuthoritySeparatelyRequired : Bool
    inspirationEqualsRepresentation : Bool
    unresolvedSourceBlocksRepresentation : Bool

open ProvenanceInstanceBoundary public

canonicalProvenanceInstanceBoundary : ProvenanceInstanceBoundary
canonicalProvenanceInstanceBoundary =
  provenanceInstanceBoundary
    true
    true
    true
    false
    true

canonicalInspirationDoesNotRepresent :
  inspirationEqualsRepresentation canonicalProvenanceInstanceBoundary
  ≡ false
canonicalInspirationDoesNotRepresent = refl

canonicalAdapterBoundary : Adapter.PhilosophyCulturalAdapter
canonicalAdapterBoundary = Adapter.canonicalPhilosophyCulturalAdapter
