module DASHI.Governance.FriendlyjordiesNarrativeGovernanceTransportExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.NarrativeClaimProvenanceExact as Narrative
import DASHI.Cognition.PNF.SensibLawITIRNarrativeComparisonTransportExact as ITIR
import DASHI.Governance.AustralianLabourMarxianContactBoundaryExact as Labour
import DASHI.Core.EmancipatoryVocabularyRelationalGrammarNoncollapseExact as Grammar

------------------------------------------------------------------------
-- FRIENDLYJORDIES PUBLIC-MEDIA PROVING CASE -> GOVERNANCE WITNESS
--
-- Source architecture comes from SensibLaw / ITIR-suite:
--   friendlyjordies_* fixtures
--   narrative_compare.py
--   public comparison contract
--
-- This file does not encode Friendlyjordies' political claims as facts.
------------------------------------------------------------------------

fjordiesSpan : ITIR.SourceSpan
fjordiesSpan = ITIR.source-span
  "jordies_case"
  "thread:Climate-Change-Politics-AU"
  "public-media / archive-backed Friendlyjordies proposition fixture"
  true

counterSpan : ITIR.SourceSpan
counterSpan = ITIR.source-span
  "counter_analysis"
  "thread:Climate-Change-Politics-AU:counter"
  "balanced / counter-analysis lane from bounded comparison fixture"
  true

cprsClaim : ITIR.AttributedProposition
cprsClaim = ITIR.attributed-proposition
  "prop:cprs:block"
  "block"
  fjordiesSpan
  "FriendlyJordies"
  "source-local authority chain preserved by fixture"
  Narrative.interpreted
  ITIR.cprsBlocking

governmentCapacityClaim : ITIR.AttributedProposition
governmentCapacityClaim = ITIR.attributed-proposition
  "prop:government:capacity"
  "support"
  fjordiesSpan
  "FriendlyJordies"
  "source-local authority chain preserved by fixture"
  Narrative.interpreted
  ITIR.governmentCapacity

counterGovernmentClaim : ITIR.AttributedProposition
counterGovernmentClaim = ITIR.attributed-proposition
  "prop:government:counter"
  "pass"
  counterSpan
  "counter-analysis"
  "source-local counter-analysis"
  Narrative.interpreted
  ITIR.governmentCapacity

supportLink : ITIR.ClaimLink
supportLink = ITIR.claim-link
  "link:jordies:cprs-government"
  ITIR.supports
  "prop:cprs:block"
  "prop:government:capacity"
  ITIR.causalSupport
  ITIR.medium
  "counter_hypothesis:policy-capacity-may-depend-on-institutional-and-electoral-conditions-beyond-cprs"
  "SensibLaw A3 causal-link provenance contract"
  true

disputeLink : ITIR.ClaimLink
disputeLink = ITIR.claim-link
  "link:comparison:government-capacity"
  ITIR.undermines
  "prop:government:capacity"
  "prop:government:counter"
  ITIR.causalDispute
  ITIR.medium
  "counter_hypothesis:shared-outcome-may-have-multiple-causal-paths"
  "SensibLaw comparison receipt: shared subject / governance-family causal dispute"
  true

jordiesLane : ITIR.NarrativeLane
jordiesLane =
  ITIR.canonicalLaneBoundary
    "jordies_case"
    (cprsClaim ∷ governmentCapacityClaim ∷ [])
    (supportLink ∷ [])

counterLane : ITIR.NarrativeLane
counterLane =
  ITIR.canonicalLaneBoundary
    "counter_analysis"
    (counterGovernmentClaim ∷ [])
    []

comparisonRow : ITIR.ComparisonRow
comparisonRow = ITIR.comparison-row
  "comparison:government-capacity"
  ITIR.disputed
  "prop:government:capacity"
  "prop:government:counter"
  "support versus pass predicates inhabit a shared government-capacity outcome family but preserve causal disagreement"
  "SensibLaw friendlyjordies_chat_arguments/thread_extract comparison fixtures"
  false

canonicalFriendlyjordiesComparison : ITIR.NarrativeComparison
canonicalFriendlyjordiesComparison =
  ITIR.canonicalComparison jordiesLane counterLane (comparisonRow ∷ [])

record GovernanceWitness : Set where
  constructor governance-witness
  field
    comparison : ITIR.NarrativeComparison
    historicalLabourContact : Labour.ContactReceipt
    vocabularyBoundary : Grammar.EmancipatoryVocabularyBoundary
    evidenceQualified : Bool
    missingnessRetained : Bool
    trajectoryInferenceClosed : Bool
    politicalVerdictIssued : Bool
    sourceNarrativePromotedToFact : Bool

open GovernanceWitness public

friendlyjordiesGovernanceWitness : GovernanceWitness
friendlyjordiesGovernanceWitness =
  governance-witness
    canonicalFriendlyjordiesComparison
    Labour.leninLaborCritique
    Grammar.canonicalEmancipatoryVocabularyBoundary
    true true false false false

friendlyjordiesComparisonPreservesDisagreement :
  ITIR.disagreementPreserved
    (comparison friendlyjordiesGovernanceWitness)
  ≡ true
friendlyjordiesComparisonPreservesDisagreement = refl

friendlyjordiesComparisonDoesNotCreateTruthScore :
  ITIR.truthScoreProduced
    (comparison friendlyjordiesGovernanceWitness)
  ≡ false
friendlyjordiesComparisonDoesNotCreateTruthScore = refl

data NarrativeClaimMayBecomeGovernanceFactWithoutReceipt : Set where
data ArgumentFamilyDeterminesPoliticalTrajectory : Set where
data FriendlyjordiesNarrativeEqualsAustralianLaborPosition : Set where
data CounterNarrativeAutomaticallyRefutesSourceNarrative : Set where

narrativeClaimDoesNotBecomeGovernanceFactWithoutReceipt :
  NarrativeClaimMayBecomeGovernanceFactWithoutReceipt → ⊥
narrativeClaimDoesNotBecomeGovernanceFactWithoutReceipt ()

argumentFamilyDoesNotDeterminePoliticalTrajectory :
  ArgumentFamilyDeterminesPoliticalTrajectory → ⊥
argumentFamilyDoesNotDeterminePoliticalTrajectory ()

friendlyjordiesDoesNotDefinitionallyEqualLaborPosition :
  FriendlyjordiesNarrativeEqualsAustralianLaborPosition → ⊥
friendlyjordiesDoesNotDefinitionallyEqualLaborPosition ()

counterNarrativeDoesNotAutomaticallyRefuteSourceNarrative :
  CounterNarrativeAutomaticallyRefutesSourceNarrative → ⊥
counterNarrativeDoesNotAutomaticallyRefuteSourceNarrative ()
