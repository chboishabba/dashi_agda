module DASHI.Culture.MissingDeceasedRosterEnrichmentDesignExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ReferencePopulationRosterEnrichmentExact as E

------------------------------------------------------------------------
-- Candidate feature definitions are fixed before control scoring.
------------------------------------------------------------------------

fusionTransitionDesign : E.MatchedReferenceDesign
fusionTransitionDesign = E.matched-reference-design
  "declared missing/deceased roster members with source-backed technical work"
  "similarly senior fusion/plasma researchers from comparable US institutions and the same time window who are not roster members"
  ("technical field" ∷ "career seniority" ∷ "institutional prominence" ∷ "publication visibility" ∷ "geography/time" ∷ [])
  true refl
  "include controls using criteria fixed before inspecting whether they satisfy fusion-transition / low-replaceability features"
  "exclude only by predeclared identity, time-window, role and data-quality rules"

capabilityBottleneckDesign : E.MatchedReferenceDesign
capabilityBottleneckDesign = E.matched-reference-design
  "source-backed technical roster"
  "matched peers in each person's institution/field/seniority band aggregated only after within-stratum matching"
  ("institution" ∷ "field" ∷ "seniority" ∷ "public visibility" ∷ "programme sensitivity" ∷ "geography/time" ∷ [])
  true refl
  "score bottleneck importance, tacit implementation knowledge, failure-mode knowledge and integration leverage using the same rubric for roster and controls"
  "do not remove controls merely because they make the roster look less unusual"

capabilitySelectorDesign : E.MatchedReferenceDesign
capabilitySelectorDesign = E.matched-reference-design
  "roster members with established public technical visibility"
  "publicly visible matched technical peers in the same capability-domain strata"
  ("public discoverability" ∷ "technical domain" ∷ "seniority" ∷ "institutional type" ∷ "time" ∷ [])
  true refl
  "test whether portfolio/advisory/funding/security/intelligence observer surfaces identify roster members at a higher rate than matched peers"
  "common internet visibility is baseline and cannot itself count as the discriminating feature"

record CurrentRosterEnrichmentFrontier : Set where
  constructor current-roster-enrichment-frontier
  field
    referencePopulationRequired : Bool
    referencePopulationRequiredIsTrue : referencePopulationRequired ≡ true

    matchedControlCountsRecovered : Bool
    matchedControlCountsRecoveredIsFalse : matchedControlCountsRecovered ≡ false

    fusionThreatRosterEnrichmentEstablished : Bool
    fusionThreatRosterEnrichmentEstablishedIsFalse :
      fusionThreatRosterEnrichmentEstablished ≡ false

    bottleneckRosterEnrichmentEstablished : Bool
    bottleneckRosterEnrichmentEstablishedIsFalse :
      bottleneckRosterEnrichmentEstablished ≡ false

    capabilityAwareSelectorEnrichmentEstablished : Bool
    capabilityAwareSelectorEnrichmentEstablishedIsFalse :
      capabilityAwareSelectorEnrichmentEstablished ≡ false

canonicalCurrentRosterEnrichmentFrontier : CurrentRosterEnrichmentFrontier
canonicalCurrentRosterEnrichmentFrontier = current-roster-enrichment-frontier
  true refl
  false refl
  false refl
  false refl
  false refl
