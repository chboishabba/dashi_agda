module DASHI.Culture.MissingDeceasedDisruptionBenefitEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.DisruptionBenefitHypothesisExact as D

------------------------------------------------------------------------
-- Source-backed historical analogue: Stuxnet / Olympic Games.
------------------------------------------------------------------------

stuxnetPrecedent : D.MultidisciplinaryDisruptionPrecedent
stuxnetPrecedent = D.multidisciplinary-disruption-precedent
  "Stuxnet / Olympic Games"
  "reported joint U.S.-Israeli operation involving NSA, CIA and Israel"
  ("cyber exploitation" ∷ "industrial control systems" ∷ "centrifuge process knowledge" ∷ "physical failure-mode targeting" ∷ [])
  "slow Iran's nuclear enrichment capability through covert technical disruption rather than conventional attack"
  D.sourceBackedHistoricalPrecedent
  "Washington Post, Ellen Nakashima and Joby Warrick, 'Stuxnet was work of U.S. and Israeli experts, officials say', 2 June 2012"
  "This establishes a historical state-level multidisciplinary sabotage precedent; it is not evidence that Israel, the United States, or any other actor caused events in this roster."

------------------------------------------------------------------------
-- Knowledge-value / replaceability hypotheses.
------------------------------------------------------------------------

loureiroValue : D.CapabilityValueProfile
loureiroValue = D.capability-value-profile
  "Nuno F. G. Loureiro"
  (D.publishedKnowledge ∷ D.tacitImplementationKnowledge ∷ D.failureModeKnowledge ∷ D.programmeIntegrationKnowledge ∷ D.lowReplaceabilityKnowledge ∷ [])
  "MIT Physics / Plasma Science and Fusion Center profiles; Viriato publication lineage"
  "Fusion confinement, transport, turbulence and magnetic reconnection are source-backed; tacit/failure/integration value remains a hypothesis to test against matched controls."

chavezValue : D.CapabilityValueProfile
chavezValue = D.capability-value-profile
  "Anthony Chavez"
  (D.tacitImplementationKnowledge ∷ D.failureModeKnowledge ∷ D.configurationKnowledge ∷ D.lowReplaceabilityKnowledge ∷ [])
  "LANL National Security Science Summer 2025 profile"
  "More than 25 years at DARHT and Scorpius design work support deep implementation experience; replaceability is not yet measured."

mccaslandValue : D.CapabilityValueProfile
mccaslandValue = D.capability-value-profile
  "William N. McCasland"
  (D.programmeIntegrationKnowledge ∷ D.technicalNetworkKnowledge ∷ D.configurationKnowledge ∷ D.lowReplaceabilityKnowledge ∷ [])
  "U.S. Air Force official biography"
  "Public career history supports unusually broad space-programme and acquisition integration; private programme knowledge is not inferred."

------------------------------------------------------------------------
-- Energy-transition relevance: fusion proper, not fusion propulsion.
------------------------------------------------------------------------

loureiroFusionEnergy : D.EnergyTransitionProfile
loureiroFusionEnergy = D.energy-transition-profile
  "Nuno Loureiro / magnetic-confinement fusion"
  D.directFusionPower
  "Commercially successful fusion could compete with incumbent fossil generation and enable downstream electrification, industrial heat or hydrogen; actor-specific economic exposure must be separately sourced."
  "MIT Physics / PSFC: confinement and transport in fusion plasmas; MIT describes the work as informing fusion devices aimed at clean, near-limitless power"
  "The hypothesis weakens if matched fusion researchers show no unusual roster enrichment or if the relevant incumbent actor lacks material exposure to fusion deployment."

leblancFissionEnergy : D.EnergyTransitionProfile
leblancFissionEnergy = D.energy-transition-profile
  "Joshua LeBlanc / fission power and space nuclear I&C"
  D.directFissionPower
  "Fission technologies can displace fossil generation in some markets, but LeBlanc's documented work is primarily space-nuclear instrumentation/control, so terrestrial fossil-displacement relevance is indirect unless a broader role is sourced."
  "NASA NTRS 20250008475"
  "Do not promote to direct terrestrial energy-transition role without a same-object source."

rezaEnergy : D.EnergyTransitionProfile
rezaEnergy = D.energy-transition-profile
  "Monica Jacinto/Reza / oxygen-compatible high-strength alloys"
  D.weakOrIndirectEnergyRelevance
  "Her patent strengthens extreme oxygen-rich propulsion/material capability; it does not by itself threaten fossil-energy demand and is a negative control against an overly broad fossil-interest narrative."
  "US20040208777A1"
  "If the proposed common feature is direct fossil displacement, Reza should count weakly or not at all unless additional source-backed energy applications are found."

------------------------------------------------------------------------
-- Beneficiary classes to investigate, not accuse.
------------------------------------------------------------------------

foreignStrategicCompetitor : D.DisruptionBeneficiaryHypothesis
foreignStrategicCompetitor = D.disruption-beneficiary-hypothesis
  "foreign strategic competitor"
  "fusion, nuclear, space, sensing or national-security technical capability"
  D.strategicDenialBenefit
  "delay or degrade a competitor's strategic technological capability or remove hard-to-replace tacit knowledge"
  "generic strategic-competition logic plus actor-specific historical precedents when sourced"
  "case-specific visibility, motive, access, temporal opportunity, communications, operational or forensic evidence"

incumbentEnergyInterest : D.DisruptionBeneficiaryHypothesis
incumbentEnergyInterest = D.disruption-beneficiary-hypothesis
  "incumbent energy interest materially exposed to fusion/fission substitution"
  "commercial fusion or other low-carbon firm power"
  D.preservesIncumbentEconomicRent
  "delay a technology that could erode generation/fuel rents if and when deployment becomes economically competitive"
  "requires company/sector exposure analysis, investment posture, lobbying/strategy records and realistic deployment economics"
  "evidence that a specific actor perceived a specific person's work as a material threat, plus access and case-specific evidence"

rivalProgrammeOrContractor : D.DisruptionBeneficiaryHypothesis
rivalProgrammeOrContractor = D.disruption-beneficiary-hypothesis
  "rival programme, contractor or funding claimant"
  "specific technical programme or contract position"
  D.shiftsFundingOrContractPosition
  "loss of a key person could delay a competitor or alter funding/contract allocation"
  "programme and procurement structure"
  "same-object competition, timing, material benefit, actor awareness and case-specific evidence"

------------------------------------------------------------------------
-- Matched-control designs.
------------------------------------------------------------------------

loureiroMatchedControl : D.MatchedControlDesign
loureiroMatchedControl = D.matched-control-design
  "Nuno Loureiro"
  ("fusion/plasma field" ∷ "career seniority" ∷ "institutional prominence" ∷ "publication visibility" ∷ "geography/time" ∷ [])
  "low replaceability + fusion-energy transition relevance + programme-integration value"
  "compare prevalence among similarly senior fusion/plasma researchers not in the roster"
  "controls must be chosen independently of knowing whether they satisfy the candidate feature"

rosterCapabilityMatchedControl : D.MatchedControlDesign
rosterCapabilityMatchedControl = D.matched-control-design
  "cross-roster"
  ("institution" ∷ "technical field" ∷ "career seniority" ∷ "public visibility" ∷ "programme sensitivity" ∷ "geography/time" ∷ [])
  "bottleneck importance + tacit implementation knowledge + failure-mode knowledge + integration leverage"
  "test whether the roster is enriched for the feature relative to matched peers"
  "do not define the feature after inspecting only positive roster cases; preserve weak/negative cases such as Reza under direct fossil-displacement hypothesis"

record CurrentDisruptionEvidenceAssessment : Set where
  constructor current-disruption-evidence-assessment
  field
    stuxnetSupportsStateTechnicalSabotagePrecedent : Bool
    stuxnetSupportsStateTechnicalSabotagePrecedentIsTrue :
      stuxnetSupportsStateTechnicalSabotagePrecedent ≡ true
    stuxnetIdentifiesActorForRoster : Bool
    stuxnetIdentifiesActorForRosterIsFalse : stuxnetIdentifiesActorForRoster ≡ false
    fusionProperHasDirectEnergyTransitionRelevance : Bool
    fusionProperHasDirectEnergyTransitionRelevanceIsTrue :
      fusionProperHasDirectEnergyTransitionRelevance ≡ true
    fossilInterestExplainsWholeRoster : Bool
    fossilInterestExplainsWholeRosterIsFalse : fossilInterestExplainsWholeRoster ≡ false
    matchedControlTestIsLive : Bool
    matchedControlTestIsLiveIsTrue : matchedControlTestIsLive ≡ true

canonicalCurrentDisruptionEvidenceAssessment : CurrentDisruptionEvidenceAssessment
canonicalCurrentDisruptionEvidenceAssessment = current-disruption-evidence-assessment
  true refl false refl true refl false refl true refl
