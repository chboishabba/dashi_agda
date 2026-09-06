module DASHI.Culture.RockhillFosterFourfoldRetreatSourceBoundaryExact where

------------------------------------------------------------------------
-- ROCKHILL / FOSTER FOURFOLD-RETREAT SOURCE BOUNDARY
--
-- Source:
--   John Bellamy Foster and Gabriel Rockhill,
--   "Western Marxism and Imperialism: A Dialogue",
--   Monthly Review 76(10), March 2025, pp. 1-25.
--
-- Public author copy:
--   https://johnbellamyfoster.org/articles/western-marxism-and-imperialism-a-dialogue/
--
-- This module records bounded source propositions and attribution boundaries.
-- It does NOT make the dialogue's historiographical claims into DASHI theorems,
-- and it does NOT classify every poststructuralist/postmodern thinker.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- The four named coordinates in the dialogue.
------------------------------------------------------------------------

data RetreatAxis : Set where
  classRetreat
  imperialismCritiqueRetreat
  natureMaterialismScienceRetreat
  reasonRetreat
  : RetreatAxis

record SourceReceipt : Set where
  constructor source-receipt
  field
    authors : String
    work : String
    publication : String
    date : String
    publicLocation : String
    boundedProposition : String
    isPrimaryForAuthorsOwnArgument : Bool
    isEmpiricalPopulationStudy : Bool
    isDASHITheorem : Bool

open SourceReceipt public

fourfoldRetreatReceipt : SourceReceipt
fourfoldRetreatReceipt =
  source-receipt
    "John Bellamy Foster; Gabriel Rockhill"
    "Western Marxism and Imperialism: A Dialogue"
    "Monthly Review 76(10), 1-25"
    "March 2025"
    "johnbellamyfoster.org author copy"
    "The dialogue characterises much of Western Marxism as an ideological field exhibiting four retreats: from class, critique of imperialism, nature/materialism/science, and reason."
    true false false

nonMechanicalFieldReceipt : SourceReceipt
nonMechanicalFieldReceipt =
  source-receipt
    "John Bellamy Foster; Gabriel Rockhill"
    "Western Marxism and Imperialism: A Dialogue"
    "Monthly Review 76(10), 1-25"
    "March 2025"
    "johnbellamyfoster.org author copy"
    "Rockhill explicitly says the four retreats do not mechanically determine every aspect of every Western Marxist discourse; positions vary across the ideological field."
    true false false

postTurnReceipt : SourceReceipt
postTurnReceipt =
  source-receipt
    "John Bellamy Foster; Gabriel Rockhill"
    "Western Marxism and Imperialism: A Dialogue"
    "Monthly Review 76(10), 1-25"
    "March 2025"
    "johnbellamyfoster.org author copy"
    "The dialogue associates the discursive turn with post-Marxism, poststructuralism and postmodernism and criticises it as a withdrawal from material reality into discourse and ideas."
    true false false

------------------------------------------------------------------------
-- Attribution / authority firewalls.
------------------------------------------------------------------------

data DialogueClaimIsUniversalClassification : Set where
data DialogueClaimIsEmpiricalPopulationLaw : Set where
data DialogueClaimIsDASHITheorem : Set where
data PoststructuralistLabelDeterminesFourRetreats : Set where

dialogueDoesNotUniversallyClassifyEveryThinker :
  DialogueClaimIsUniversalClassification → ⊥
dialogueDoesNotUniversallyClassifyEveryThinker ()

dialogueIsNotEmpiricalPopulationLaw :
  DialogueClaimIsEmpiricalPopulationLaw → ⊥
dialogueIsNotEmpiricalPopulationLaw ()

dialogueIsNotDASHITheorem : DialogueClaimIsDASHITheorem → ⊥
dialogueIsNotDASHITheorem ()

poststructuralistLabelDoesNotDetermineFourRetreats :
  PoststructuralistLabelDeterminesFourRetreats → ⊥
poststructuralistLabelDoesNotDetermineFourRetreats ()

record FourfoldRetreatSourceBoundary : Set where
  constructor fourfold-retreat-source-boundary
  field
    fourNamedAxesRecovered : Bool
    fieldIsExplicitlyNonMechanical : Bool
    poststructuralismIsCriticisedInDialogue : Bool
    sourceIsPrimaryForAuthorsArgument : Bool
    sourceIsEmpiricalPopulationStudy : Bool
    everyPoststructuralistHasAllFourRetreats : Bool
    DASHIFormalisationAttributedToAuthors : Bool

canonicalFourfoldRetreatSourceBoundary : FourfoldRetreatSourceBoundary
canonicalFourfoldRetreatSourceBoundary =
  fourfold-retreat-source-boundary
    true true true true false false false
