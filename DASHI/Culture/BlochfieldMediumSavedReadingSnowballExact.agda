module DASHI.Culture.BlochfieldMediumSavedReadingSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Culture.BlochfieldCreatorGenealogySnowballExact as Creator

------------------------------------------------------------------------
-- BLOCHFIELD MEDIUM SAVED-READING SNOWBALL
--
-- The unresolved same-name Medium candidate contains a 2024 "Provocations"
-- list with one saved 2023 Dark Matter Labs article.  This is useful historical
-- acquisition context, but the account-to-@msiyasmsi identity weld is unpaid.
-- A saved/listed reading is therefore NOT creator authorship, endorsement,
-- derivation, Blochfield ancestry, or same-object technical lineage.
------------------------------------------------------------------------

darkMatterLabsRadicleCivicsSource : Attribution.AttributedSource
darkMatterLabsRadicleCivicsSource =
  Attribution.mkNoDOISource
    "Alexandra Bekker; Calvin Po; Fang-Jui ‘Fang-Raye’ Chang"
    "Radicle Civics — Building Proofs of Possibilities for a Civic Economy and Society"
    "Dark Matter Labs / Provocations"
    "2023"
    "https://provocations.darkmatterlabs.org/radicle-civics-building-proofs-of-possibilities-for-a-civic-economy-and-society-ee28baeeec70"
    Attribution.practitionerSource
    ("Historical saved-reading candidate reached through the unresolved same-name Medium account. " ++
     "The source discusses civic infrastructures, path dependence, relational systems and proofs of possibilities, " ++
     "but is not promoted into Blochfield ancestry, creator citation, endorsement or derivation.")
    Attribution.publicAttribution

radicleCivicsDOI : String
radicleCivicsDOI = "no DOI recorded in the inspected Dark Matter Labs web manifestation"

radicleCivicsQID : String
radicleCivicsQID = "unresolved"

radicleCivicsDewey : String
radicleCivicsDewey = "unresolved"

record MediumSavedReadingCandidate : Set where
  constructor medium-saved-reading-candidate
  field
    mediumCandidate : Creator.CrossPlatformIdentityCandidate
    savedReading : Attribution.AttributedSource
    listReference : String
    listDateReported : String
    articleDateReported : String
    mediumSamePersonIdentityPaid : Bool
    mediumSamePersonIdentityPaidIsFalse : mediumSamePersonIdentityPaid ≡ false
    savedReadingEndorsementPaid : Bool
    savedReadingEndorsementPaidIsFalse : savedReadingEndorsementPaid ≡ false
    blochfieldDerivationPaid : Bool
    blochfieldDerivationPaidIsFalse : blochfieldDerivationPaid ≡ false
    sameObjectTechnicalLineagePaid : Bool
    sameObjectTechnicalLineagePaidIsFalse : sameObjectTechnicalLineagePaid ≡ false

open MediumSavedReadingCandidate public

mediumSavedRadicleCivicsCandidate : MediumSavedReadingCandidate
mediumSavedRadicleCivicsCandidate =
  medium-saved-reading-candidate
    Creator.mediumIdentityCandidate
    darkMatterLabsRadicleCivicsSource
    "https://medium.com/@yasminanacreto/list/80f317ad2598"
    "2024-03-31"
    "2023-08-14"
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Payment remains ordered.  This acquired reading does not pay the identity
-- weld or native creator-material leaves upstream of any ancestry conclusion.
------------------------------------------------------------------------

sameNameMediumIdentityStillUnpaid : Creator.GenealogyStanding
sameNameMediumIdentityStillUnpaid =
  Creator.genealogyStanding Creator.crossPlatformIdentityWeld

creatorLongFormStillUnpaid : Creator.GenealogyStanding
creatorLongFormStillUnpaid =
  Creator.genealogyStanding Creator.creatorLongFormExplanation

creatorExplicitReferencesStillUnpaid : Creator.GenealogyStanding
creatorExplicitReferencesStillUnpaid =
  Creator.genealogyStanding Creator.creatorExplicitReferences

externalSameObjectLineageStillUnpaid : Creator.GenealogyStanding
externalSameObjectLineageStillUnpaid =
  Creator.genealogyStanding Creator.externalSameObjectLineage

------------------------------------------------------------------------
-- WrongType / non-promotion firewalls.
------------------------------------------------------------------------

data SavedReadingPaysCreatorLineage : Set where
data SavedReadingPaysCreatorEndorsement : Set where
data SameNameMediumSavedReadingPaysSamePerson : Set where
data IndependentArticleConceptsPayBlochfieldDerivation : Set where

savedReadingDoesNotPayCreatorLineage :
  SavedReadingPaysCreatorLineage → ⊥
savedReadingDoesNotPayCreatorLineage ()

savedReadingDoesNotPayCreatorEndorsement :
  SavedReadingPaysCreatorEndorsement → ⊥
savedReadingDoesNotPayCreatorEndorsement ()

sameNameMediumSavedReadingDoesNotPaySamePerson :
  SameNameMediumSavedReadingPaysSamePerson → ⊥
sameNameMediumSavedReadingDoesNotPaySamePerson ()

independentArticleConceptsDoNotPayBlochfieldDerivation :
  IndependentArticleConceptsPayBlochfieldDerivation → ⊥
independentArticleConceptsDoNotPayBlochfieldDerivation ()

------------------------------------------------------------------------
-- Semantic checksum:
--
--   saved reading != authored reading
--   saved reading != endorsement
--   same-name Medium account != @msiyasmsi identity
--   conceptual adjacency != Blochfield genealogy
--
-- The useful acquisition result is historical reachability: if the Medium
-- identity weld is ever paid, this 2023 reading becomes a creator-library
-- coordinate worth checking for explicit downstream reuse.  Until then it is
-- retained out of order and cannot move the conclusion-paying frontier.
------------------------------------------------------------------------
