module DASHI.Culture.BlochfieldAcquisitionResidualSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Culture.BlochfieldCreatorGenealogySnowballExact as Creator

------------------------------------------------------------------------
-- BLOCHFIELD ACQUISITION RESIDUAL / REVERSE-ANALOGUE CONTROL
--
-- This owner records failed creator-material discovery routes so they remain
-- useful acquisition history without becoming absence claims.  It also admits
-- reverse-search conceptual analogues without letting resemblance become
-- genealogy, derivation, same-object identity, or technical payment.
------------------------------------------------------------------------

record SearchAcquisitionResidual : Set where
  constructor search-acquisition-residual
  field
    retrievalDate : String
    queryReference : String
    searchedCoordinates : String
    sameObjectCreatorMaterialLocated : Bool
    sameObjectCreatorMaterialLocatedIsFalse :
      sameObjectCreatorMaterialLocated ≡ false
    searchNonLocationCreatesKnownAbsence : Bool
    searchNonLocationCreatesKnownAbsenceIsFalse :
      searchNonLocationCreatesKnownAbsence ≡ false

open SearchAcquisitionResidual public

exactPhraseSearchNonLocation : SearchAcquisitionResidual
exactPhraseSearchNonLocation =
  search-acquisition-residual
    "2026-09-12"
    "public web exact/status-id discovery tranche"
    ("2090447851625050481 | @msiyasmsi Blochfield | " ++
     "protects change from becoming epistemically destructive | " ++
     "boundary-conservative transfiguration | A boundary may disappear lawfully")
    false refl
    false refl

-- The repo OSINT invariant already owns the general rule.  This local empty
-- type makes the Blochfield application explicit for downstream consumers.
data SearchNonLocationProvesCreatorMaterialAbsent : Set where

searchNonLocationDoesNotProveAbsence :
  SearchNonLocationProvesCreatorMaterialAbsent → ⊥
searchNonLocationDoesNotProveAbsence ()

------------------------------------------------------------------------
-- Reverse conceptual analogue: topological protection.
--
-- Search surfaced ordinary topologically protected / obstructed-mode
-- literature because the meme uses that vocabulary.  This is useful as a
-- comparator for what the source explicitly contrasts itself against, but it
-- is NOT evidence that the creator cited, derived from, or intended this paper.
------------------------------------------------------------------------

reverseTopologicalAnalogueCandidate : Attribution.AttributedSource
reverseTopologicalAnalogueCandidate =
  Attribution.mkDOISource
    "L. Q. English; A. Halchenko; F. Palmero"
    "Topologically protected spatially localized modes: An easy experimental realization of the Su-Schrieffer-Heeger model"
    "Physica B: Condensed Matter 734, 418616"
    "2026"
    "10.1016/j.physb.2026.418616"
    "https://www.sciencedirect.com/science/article/pii/S0921452626003741"
    Attribution.academicArticleSource
    ("Reverse-search conceptual analogue for ordinary topological protection only; " ++
     "not creator citation, ancestry, same-object lineage, or Blochfield technical support.")
    Attribution.publicAttribution

record ReverseAnalogueAdmission : Set where
  constructor reverse-analogue-admission
  field
    source : Attribution.AttributedSource
    relation : String
    creatorCitationPaid : Bool
    creatorCitationPaidIsFalse : creatorCitationPaid ≡ false
    derivationPaid : Bool
    derivationPaidIsFalse : derivationPaid ≡ false
    sameObjectLineagePaid : Bool
    sameObjectLineagePaidIsFalse : sameObjectLineagePaid ≡ false

reverseTopologicalAnalogueAdmission : ReverseAnalogueAdmission
reverseTopologicalAnalogueAdmission =
  reverse-analogue-admission
    reverseTopologicalAnalogueCandidate
    "contrasted vocabulary / reverse conceptual analogue"
    false refl
    false refl
    false refl

data ConceptualResemblanceCreatesBlochfieldLineage : Set where

data ReverseSearchHitPaysCreatorCitation : Set where

conceptualResemblanceDoesNotCreateLineage :
  ConceptualResemblanceCreatesBlochfieldLineage → ⊥
conceptualResemblanceDoesNotCreateLineage ()

reverseSearchHitDoesNotPayCreatorCitation :
  ReverseSearchHitPaysCreatorCitation → ⊥
reverseSearchHitDoesNotPayCreatorCitation ()

------------------------------------------------------------------------
-- Current payment frontier.
--
-- Failed indexed searches and reverse analogues do not move the first
-- conclusion-paying leaf.  Native creator material remains the wall.
------------------------------------------------------------------------

nativeCreatorMaterialStillFirstPayingLeaf : Creator.GenealogyStanding
nativeCreatorMaterialStillFirstPayingLeaf =
  Creator.genealogyStanding Creator.nativeXProfileReceipt

nativeWebsiteStillUnpaid : Creator.GenealogyStanding
nativeWebsiteStillUnpaid =
  Creator.genealogyStanding Creator.nativeBlochfieldWebsiteContent

creatorLongFormStillUnpaid : Creator.GenealogyStanding
creatorLongFormStillUnpaid =
  Creator.genealogyStanding Creator.creatorLongFormExplanation

externalSameObjectLineageStillUnpaid : Creator.GenealogyStanding
externalSameObjectLineageStillUnpaid =
  Creator.genealogyStanding Creator.externalSameObjectLineage

------------------------------------------------------------------------
-- Semantic checksum:
--
--   search non-location != known absence
--   conceptual resemblance != genealogy
--   reverse-search analogue != creator citation
--   discovery breadth != conclusion payment
------------------------------------------------------------------------
