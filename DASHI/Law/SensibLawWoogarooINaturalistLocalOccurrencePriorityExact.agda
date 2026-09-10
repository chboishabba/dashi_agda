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
  ecologicalContextCandidate
  "Research-grade same-locality biodiversity evidence; useful for local assemblage/context, not presently a threatened-species legal atom."
  "Acquire exact coordinate/accuracy only if used in a spatial biodiversity-density or same-corridor analysis."

scarlet364188331 : PrioritisedOccurrence
scarlet364188331 = prioritised-occurrence
  "364188331"
  "Myzomela sanguinolenta / Scarlet Honeyeater"
  "Research Grade"
  "Brookwater QLD 4300"
  ecologicalContextCandidate
  "Research-grade native bird occurrence in the broader Brookwater landscape."
  "Exact coordinate/accuracy required before any project/corridor intersection claim."

blackCockatoo357433327 : PrioritisedOccurrence
blackCockatoo357433327 = prioritised-occurrence
  "357433327"
  "Zanda / Yellow-tailed and White-tailed Black Cockatoos"
  "Needs ID"
  "Brookwater Dr at Greg Norman Circuit, Brookwater QLD 4300"
  conservationLegalCandidate
  "Potentially useful native-fauna occurrence because the current record is only genus-level and therefore can open an identification/acquisition edge."
  "Resolve species-level identification before assigning any conservation status or legal significance."

unknownAudio321370246 : PrioritisedOccurrence
unknownAudio321370246 = prioritised-occurrence
  "321370246"
  "Unknown; saved page indicates an audio-bearing observation"
  "Casual"
  "saved locality must be read from the individual observation before spatial use"
  conservationLegalCandidate
  "Audio-bearing unknowns can be higher-alpha than already-common taxa because later identification may reveal a useful species occurrence."
  "Acquire individual observation, audio, location, date and community/expert identifications."

unknownAudio374519427 : PrioritisedOccurrence
unknownAudio374519427 = prioritised-occurrence
  "374519427"
  "Unknown; saved page indicates an audio-bearing observation"
  "Casual"
  "saved locality must be read from the individual observation before spatial use"
  conservationLegalCandidate
  "Retain as an identification Snowball edge rather than discard merely because the current taxon is unknown."
  "Acquire individual observation, audio, location, date and community/expert identifications."

------------------------------------------------------------------------
-- Priority policy and firewalls.
------------------------------------------------------------------------

record LocalOccurrencePriorityPolicy : Set where
  constructor local-occurrence-priority-policy
  field
    prioritiseListedOrPotentiallyListedTaxa : Bool
    prioritiseAudioUnknownsForIdentification : Bool
    prioritiseResearchGradeForContext : Bool
    requireExactCoordinateBeforeProjectJoin : Bool
    preserveNeedsIdAsOpenAcquisitionEdge : Bool
    prohibitQualityGradeToLegalStatusCollapse : Bool
    prohibitLocalityLabelToProjectIntersectionCollapse : Bool
    prohibitGenusToSpeciesStatusCollapse : Bool

open LocalOccurrencePriorityPolicy public

canonicalLocalOccurrencePriorityPolicy : LocalOccurrencePriorityPolicy
canonicalLocalOccurrencePriorityPolicy = local-occurrence-priority-policy
  true true true true true true true true

data ResearchGradeCreatesLegalTrigger : Set where

data SavedLocalityCreatesProjectIntersection : Set where

data GenusIdentificationCreatesSpeciesStatus : Set where

data LocalBiodiversityAutomaticallyPaysCriticalHabitat : Set where

noResearchGradeLegalCollapse : ResearchGradeCreatesLegalTrigger → ⊥
noResearchGradeLegalCollapse ()

noLocalityIntersectionCollapse : SavedLocalityCreatesProjectIntersection → ⊥
noLocalityIntersectionCollapse ()

noGenusStatusCollapse : GenusIdentificationCreatesSpeciesStatus → ⊥
noGenusStatusCollapse ()

noBiodiversityCriticalHabitatCollapse : LocalBiodiversityAutomaticallyPaysCriticalHabitat → ⊥
noBiodiversityCriticalHabitatCollapse ()
