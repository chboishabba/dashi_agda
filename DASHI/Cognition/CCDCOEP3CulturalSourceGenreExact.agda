{-# OPTIONS --safe #-}
module DASHI.Cognition.CCDCOEP3CulturalSourceGenreExact where

-- Original authorship: Oreskes/Conway, Klein/Taylor, Chomsky/Pollin,
-- Polychroniou, Mann, Michaels, Washington/Cook, Gibbs, McKay, Kenner.
-- Their claims, films and books remain independently authored.
-- Existing original Oreskes/Conway owners in DASHI.Governance remain
-- authoritative; this module adds only genre/source-status boundaries.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

data WorkKind : Set where
  historicalResearch : WorkKind
  politicalInterpretation : WorkKind
  policyProposal : WorkKind
  documentaryArgument : WorkKind
  fictionalSatire : WorkKind

data SourceStatus : Set where
  bibliographicLocator : SourceStatus
  publishedInterpretation : SourceStatus
  independentlyVerifiedObservation : SourceStatus
  identifiedRealWorldCausalEffect : SourceStatus

record CulturalWork : Set where
  constructor culturalWork
  field
    kind : WorkKind
    status : SourceStatus

merchantsBook : CulturalWork
merchantsBook = culturalWork historicalResearch publishedInterpretation

kleinTaylor2026 : CulturalWork
kleinTaylor2026 = culturalWork politicalInterpretation bibliographicLocator

chomskyPollin2020 : CulturalWork
chomskyPollin2020 = culturalWork policyProposal bibliographicLocator

planetOfHumans2020 : CulturalWork
planetOfHumans2020 = culturalWork documentaryArgument bibliographicLocator

dontLookUp2021 : CulturalWork
dontLookUp2021 = culturalWork fictionalSatire bibliographicLocator

historicalResearchNotFiction :
  CulturalWork.kind merchantsBook ≡ fictionalSatire → ⊥
historicalResearchNotFiction ()

policyProposalNotHistoricalObservation :
  CulturalWork.kind chomskyPollin2020 ≡ historicalResearch → ⊥
policyProposalNotHistoricalObservation ()

documentaryNotCausalProof :
  CulturalWork.status planetOfHumans2020 ≡ identifiedRealWorldCausalEffect → ⊥
documentaryNotCausalProof ()

satireNotEmpiricalObservation :
  CulturalWork.status dontLookUp2021 ≡ independentlyVerifiedObservation → ⊥
satireNotEmpiricalObservation ()

kleinTaylorBibliographyNotCausalProof :
  CulturalWork.status kleinTaylor2026 ≡ identifiedRealWorldCausalEffect → ⊥
kleinTaylorBibliographyNotCausalProof ()
