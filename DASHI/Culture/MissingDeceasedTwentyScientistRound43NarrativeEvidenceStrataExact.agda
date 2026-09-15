module DASHI.Culture.MissingDeceasedTwentyScientistRound43NarrativeEvidenceStrataExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistRound42ExactKeyCrossingSurfaceExact as R42

------------------------------------------------------------------------
-- ROUND 43: NARRATIVE / EVIDENCE STRATA
--
-- The investigation now contains enough exact objects that a narrative can be
-- stated, but only if epistemic levels remain explicit.  Directly sourced
-- propositions, bounded synthesis, and unsupported claims are therefore kept
-- in separate strata.  Narrative convenience cannot skip H2/H3 promotion.
------------------------------------------------------------------------

data NarrativeStatus : Set where
  directlyEvidenced
  boundedInference
  unsupported : NarrativeStatus

record NarrativeProposition : Set where
  constructor narrative-proposition
  field
    status : NarrativeStatus
    proposition : String
    basis : String
    boundary : String

open NarrativeProposition public

directEvidenceNarrative : List NarrativeProposition
directEvidenceNarrative =
  narrative-proposition directlyEvidenced
    "The retained cohort contains scientists and engineers attached to concrete technical objects spanning propulsion, fission power, flash radiography, materials, astronomy, autonomy, sensing, biotechnology and related high-technology domains."
    "Rounds 23-42 retain exact project, grant, WBS, patent, programme, publication, facility, instrument and contract identifiers for many rows."
    "Technical significance and strategic relevance are object-local; this does not establish one shared programme or one cause of death/disappearance."
  ∷ narrative-proposition directlyEvidenced
    "Several rows involve government, defence, aerospace, national-laboratory, space, military-university or nationally funded research settings."
    "Examples include LANL DARHT/Scorpius, NASA FSP/JPL/MSFC surfaces, AFRL HCB, Army DAAH01-01-9-R001, NUDT objects, NPU NSFC-funded hypersonics and related institutional records."
    "Institutional mission overlap is not equivalent to shared task identity, secrecy, targeting or coordination."
  ∷ narrative-proposition directlyEvidenced
    "The searched exact-key surface currently contains no paid literal two-retained-person same-object receipt."
    "Round 42 searched six refreshed exact identifiers/families and retained earlier HCB/Amy/Ning/NUDT/JPL negative controls."
    "This is a bounded searched-surface result, not proof that no such link exists anywhere."
  ∷ []

boundedInferenceNarrative : List NarrativeProposition
boundedInferenceNarrative =
  narrative-proposition boundedInference
    "The best current cohort-level description is a distributed collection of high-value technical programmes with thematic, institutional and mission adjacency rather than one demonstrated common programme."
    "Many exact single-person objects are paid while H2 remains zero across the cohort."
    "This is a model-selection statement about currently acquired evidence, not a universal historical claim."
  ∷ narrative-proposition boundedInference
    "The most informative future evidence is identity-bearing exact-object material rather than additional broad biographical or strategic-context evidence."
    "Across multiple rows the live defect is consistently the missing crossing identifier, roster, work package, contract role, grant link, facility record or primary closeout/review object."
    "Search prioritisation is a DASHI synthesis and carries no external source authority."
  ∷ []

unsupportedNarrative : List NarrativeProposition
unsupportedNarrative =
  narrative-proposition unsupported
    "The 20 scientists belonged to one hidden programme or coordinated network."
    "No literal cohort-wide shared-object receipt has been paid."
    "H2 remains zero."
  ∷ narrative-proposition unsupported
    "Their deaths, disappearances or losses were caused by their research, by a state actor, by an industry actor, or by a coordinated suppression effort."
    "No pre-event operational targeting/security/custody receipt has been paid on a shared object."
    "H3 remains zero; temporal or thematic concentration cannot substitute for operational evidence."
  ∷ narrative-proposition unsupported
    "Missing public records, restricted meetings, defence relevance or search failure demonstrate concealment or classification."
    "The current record contains several acquisition gaps and restricted/public-boundary surfaces."
    "Absence, restriction and search failure are not positive evidence of concealment, classification or wrongdoing."
  ∷ []

round43DirectEvidenceCount : Nat
round43DirectEvidenceCount = 3

round43BoundedInferenceCount : Nat
round43BoundedInferenceCount = 2

round43UnsupportedCount : Nat
round43UnsupportedCount = 3

narrativeCannotSkipPromotionGate : Bool
narrativeCannotSkipPromotionGate = true

strategicRelevanceCannotPayCommonProgramme : Bool
strategicRelevanceCannotPayCommonProgramme = true

commonProgrammeWouldStillNotPayTargeting : Bool
commonProgrammeWouldStillNotPayTargeting = true

absenceCannotPayConcealment : Bool
absenceCannotPayConcealment = true

sourceAttributionDoesNotTransferAcrossNarrativeStrata : Bool
sourceAttributionDoesNotTransferAcrossNarrativeStrata = true

round43H2PaidCount : Nat
round43H2PaidCount = 0

round43H3PaidCount : Nat
round43H3PaidCount = 0

round43CurrentNarrative : String
round43CurrentNarrative = "The acquired record supports a heterogeneous cohort of people working on concrete and often technically consequential programmes, some of them defence-, aerospace-, state-, national-laboratory- or national-funding-adjacent. Exact-key search has substantially improved object identity but has not yet produced a literal two-retained-person same-object receipt. The strongest evidence-bounded narrative is therefore distributed high-value technical programmes with pockets of thematic/institutional adjacency, not one demonstrated hidden programme. No evidence-bounded narrative presently supports coordinated targeting, suppression, concealment or common causation."

round43Discriminator : String
round43Discriminator = "A single literal H2 receipt would change the programme-network narrative for the linked pair but would still not support H3. A pre-event operational/security/custody receipt tied to that same paid shared object would be required before any targeting narrative became admissible."
