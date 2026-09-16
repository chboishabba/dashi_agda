module DASHI.Law.SensibLawWoogarooINaturalistLocalOccurrencePriorityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Local iNaturalist occurrence prioritisation for the Woogaroo corpus.
--
-- Source carrier: observer-supplied saved iNaturalist HTML for user johl1.
-- Counts are deduplicated by native observation ID across the three saved
-- observation pages. Quality grade improves identification confidence but
-- does not itself create legal relevance, statutory status or project GIS
-- intersection.
------------------------------------------------------------------------

data OccurrencePriority : Set where
  conservationLegalCandidate : OccurrencePriority
  ecologicalContextCandidate : OccurrencePriority
  nonSpatialAcquisitionCandidate : OccurrencePriority
  lowImmediateLegalValue : OccurrencePriority

record LocalCorpusSummary : Set where
  constructor local-corpus-summary
  field
    uniqueProfileObservations : Nat
    locallyLabelledObservations : Nat
    localResearchGrade : Nat
    localNeedsIdOrCasual : Nat
    localDefinition : String
    provenance : String

open LocalCorpusSummary public

johl1LocalCorpus : LocalCorpusSummary
johl1LocalCorpus = local-corpus-summary
  114
  76
  25
  51
  "Saved locality label contains Brookwater, Springfield, Springfield Central, Spring Mountain, Augustine Heights or Bellbird Park."
  "Derived by deduplicating native iNaturalist observation IDs across the three observer-supplied saved observation pages."

record PrioritisedOccurrence : Set where
  constructor prioritised-occurrence
  field
    observationId : String
    taxonReading : String
    qualityReading : String
    localityReading : String
    dateReading : String
    mediaReading : String
    priority : OccurrencePriority
    boundedUse : String
    residual : String

open PrioritisedOccurrence public

calomela388681275 : PrioritisedOccurrence
calomela388681275 = prioritised-occurrence
  "388681275"
  "Calomela juncta"
  "Research Grade"
  "Brookwater Dr at Greg Norman Circuit, Brookwater QLD 4300"
  "2026-08-06 16:17 AEST"
  "photo-bearing saved observation"
  ecologicalContextCandidate
  "Research-grade same-locality biodiversity evidence; useful for local assemblage/context, not presently a threatened-species legal atom."
  "Acquire exact coordinate/accuracy only if used in a spatial biodiversity-density or same-corridor analysis."

scarlet364188331 : PrioritisedOccurrence
scarlet364188331 = prioritised-occurrence
  "364188331"
  "Myzomela sanguinolenta / Scarlet Honeyeater"
  "Research Grade"
  "Brookwater QLD 4300"
  "2026-05-23 15:16 AEST"
  "saved observation includes media"
  ecologicalContextCandidate
  "Research-grade native bird occurrence in the broader Brookwater landscape."
  "Exact coordinate/accuracy required before any project/corridor intersection claim."

blackCockatoo357433327 : PrioritisedOccurrence
blackCockatoo357433327 = prioritised-occurrence
  "357433327"
  "Zanda / Yellow-tailed and White-tailed Black Cockatoos"
  "Needs ID"
  "Brookwater Dr at Greg Norman Circuit, Brookwater QLD 4300"
  "2026-05-02 16:36 AEST"
  "photo and audio icons visible in saved page"
  ecologicalContextCandidate
  "Native-fauna occurrence with unresolved species identity; useful as a species-resolution acquisition edge, but genus-level identification does not pay a threatened-species proposition."
  "Resolve species-level identification and exact coordinate/accuracy before assigning conservation or project significance."

unknownAudio321370246 : PrioritisedOccurrence
unknownAudio321370246 = prioritised-occurrence
  "321370246"
  "Unknown; saved page indicates an audio-bearing observation"
  "Casual"
  "Missing Location"
  "Missing Date"
  "audio icon visible in saved page"
  nonSpatialAcquisitionCandidate
  "Retain because later identification may be useful, but the saved carrier supplies neither date nor location and therefore it is not a local Woogaroo occurrence receipt."
  "Acquire individual observation metadata and audio; do not spatially promote unless date/location are recovered."

unknownAudio374519427 : PrioritisedOccurrence
unknownAudio374519427 = prioritised-occurrence
  "374519427"
  "Unknown; saved page indicates an audio-bearing observation"
  "Casual"
  "Missing Location"
  "Missing Date"
  "audio icon visible in saved page"
  nonSpatialAcquisitionCandidate
  "Retain as an identification Snowball edge, but the saved carrier does not locate it in the Woogaroo landscape."
  "Acquire individual observation metadata and audio; do not spatially promote unless date/location are recovered."

kingParrot331651806 : PrioritisedOccurrence
kingParrot331651806 = prioritised-occurrence
  "331651806"
  "Alisterus scapularis / Australian King Parrot"
  "Research Grade"
  "Grand Ave at Applecross Cct, Spring Mountain QLD 4300"
  "2025-11-24 17:30 AEST"
  "photo-bearing saved observation"
  ecologicalContextCandidate
  "Research-grade native bird occurrence in the southern local landscape; useful as ecological context rather than a threatened-species legal atom."
  "Acquire exact coordinate/accuracy only if used in corridor assemblage analysis."

redNeckedWallaby324838582 : PrioritisedOccurrence
redNeckedWallaby324838582 = prioritised-occurrence
  "324838582"
  "Notamacropus rufogriseus / Red-necked Wallaby"
  "Research Grade"
  "Springfield QLD 4300"
  "2025-11-04 18:04 AEST"
  "photo-bearing saved observation"
  ecologicalContextCandidate
  "Research-grade terrestrial-fauna occurrence in the broader Springfield landscape."
  "Exact coordinate/accuracy required before any habitat-corridor or project-footprint use."

------------------------------------------------------------------------
-- Priority policy and firewalls.
------------------------------------------------------------------------

record LocalOccurrencePriorityPolicy : Set where
  constructor local-occurrence-priority-policy
  field
    prioritiseListedOrPotentiallyListedTaxa : Bool
    retainUnresolvedMediaForIdentification : Bool
    prioritiseResearchGradeForContext : Bool
    requireExactCoordinateBeforeProjectJoin : Bool
    preserveNeedsIdAsOpenAcquisitionEdge : Bool
    prohibitQualityGradeToLegalStatusCollapse : Bool
    prohibitLocalityLabelToProjectIntersectionCollapse : Bool
    prohibitGenusToSpeciesStatusCollapse : Bool
    prohibitMissingLocationToLocalOccurrenceCollapse : Bool

open LocalOccurrencePriorityPolicy public

canonicalLocalOccurrencePriorityPolicy : LocalOccurrencePriorityPolicy
canonicalLocalOccurrencePriorityPolicy = local-occurrence-priority-policy
  true true true true true true true true true

data ResearchGradeCreatesLegalTrigger : Set where

data SavedLocalityCreatesProjectIntersection : Set where

data GenusIdentificationCreatesSpeciesStatus : Set where

data LocalBiodiversityAutomaticallyPaysCriticalHabitat : Set where

data MissingLocationCreatesWoogarooOccurrence : Set where

noResearchGradeLegalCollapse : ResearchGradeCreatesLegalTrigger → ⊥
noResearchGradeLegalCollapse ()

noLocalityIntersectionCollapse : SavedLocalityCreatesProjectIntersection → ⊥
noLocalityIntersectionCollapse ()

noGenusStatusCollapse : GenusIdentificationCreatesSpeciesStatus → ⊥
noGenusStatusCollapse ()

noBiodiversityCriticalHabitatCollapse : LocalBiodiversityAutomaticallyPaysCriticalHabitat → ⊥
noBiodiversityCriticalHabitatCollapse ()

noMissingLocationCollapse : MissingLocationCreatesWoogarooOccurrence → ⊥
noMissingLocationCollapse ()
