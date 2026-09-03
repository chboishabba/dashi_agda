module DASHI.Culture.MissingDeceasedCounterfactualDisruptionImpactExact where

open import DASHI.Core.Prelude

import DASHI.Core.CounterfactualDisruptionImpactExact as Impact

------------------------------------------------------------------------
-- Case-specific impact searches.  Current status is notLocated: the public
-- technical-role evidence establishes expertise, not the counterfactual impact
-- of losing that expertise.
------------------------------------------------------------------------

loureiroImpact : Impact.DepartureImpactProfile
loureiroImpact = Impact.departure-impact-profile
  "Nuno F. G. Loureiro"
  "MIT Plasma Science and Fusion Center / fusion-plasma research capability"
  (Impact.milestoneDelay ∷ Impact.replacementLatency ∷ Impact.knowledgeTransferGap ∷ Impact.programmeReorganisation ∷ [])
  Impact.impactNotLocated
  "need pre/post programme schedules, succession/replacement records, project milestones, group reorganisation and contemporaneous institutional accounts"
  "leadership and scientific prominence do not by themselves establish disproportionate disruption"

chavezImpact : Impact.DepartureImpactProfile
chavezImpact = Impact.departure-impact-profile
  "Anthony Chavez"
  "DARHT / Scorpius accelerator engineering"
  (Impact.replacementLatency ∷ Impact.uniqueQualificationLoss ∷ Impact.knowledgeTransferGap ∷ Impact.milestoneDelay ∷ [])
  Impact.impactNotLocated
  "need role/succession records, unique qualification or subsystem ownership evidence, Scorpius milestone effects and replacement timing"
  "25+ years of experience motivates the test but is not itself a measured impact receipt"

mccaslandImpact : Impact.DepartureImpactProfile
mccaslandImpact = Impact.departure-impact-profile
  "William N. McCasland"
  "space-system / programme-integration knowledge"
  (Impact.programmeReorganisation ∷ Impact.knowledgeTransferGap ∷ Impact.fundingOrContractShift ∷ Impact.replacementLatency ∷ [])
  Impact.impactNotLocated
  "need exact contemporaneous programme/role at time of disappearance, succession, programme-management consequences and any post-loss restructuring"
  "historical breadth of career does not prove that a current programme depended on him at the relevant time"

leblancImpact : Impact.DepartureImpactProfile
leblancImpact = Impact.departure-impact-profile
  "Joshua LeBlanc"
  "NASA space nuclear instrumentation and control technology maturation"
  (Impact.replacementLatency ∷ Impact.knowledgeTransferGap ∷ Impact.milestoneDelay ∷ [])
  Impact.impactNotLocated
  "need team-role continuity, replacement assignment, milestone changes and I&C technology-maturation schedule before/after loss"
  "named technical-lead role motivates a key-person test; it does not settle it"

rezaImpact : Impact.DepartureImpactProfile
rezaImpact = Impact.departure-impact-profile
  "Monica Jacinto / Monica Reza"
  "oxygen-compatible high-strength alloy / propulsion-material knowledge"
  (Impact.knowledgeTransferGap ∷ Impact.technicalPerformanceLoss ∷ Impact.replacementLatency ∷ [])
  Impact.impactNotLocated
  "need evidence of active programme ownership at relevant time, untransferred know-how, successor work and any delayed materials qualification"
  "patent inventorship establishes contribution but not continuing key-person dependency"

------------------------------------------------------------------------
-- Matched departure designs.
------------------------------------------------------------------------

loureiroDepartureControl : Impact.MatchedDepartureControl
loureiroDepartureControl = Impact.matched-departure-control
  loureiroImpact
  ("fusion/plasma field" ∷ "seniority" ∷ "leadership role" ∷ "institutional scale" ∷ "time period" ∷ [])
  "comparable senior fusion/plasma researchers leaving roles through retirement, recruitment, illness, death or ordinary turnover"
  "milestone delay, replacement latency, reorganisation and knowledge-transfer gap measured with the same definitions"
  "predefined pre/post window"
  "control departures must be selected without conditioning on whether disruption was large or small"

chavezDepartureControl : Impact.MatchedDepartureControl
chavezDepartureControl = Impact.matched-departure-control
  chavezImpact
  ("specialized facility engineering" ∷ "tenure" ∷ "technical responsibility" ∷ "programme phase" ∷ [])
  "comparable long-tenure accelerator/facility engineers leaving high-energy experimental programmes"
  "replacement latency, unique qualification loss and milestone consequences"
  "predefined pre/post window"
  "do not choose controls for having unusually smooth succession"

crossRosterDepartureControl : Impact.MatchedDepartureControl
crossRosterDepartureControl = Impact.matched-departure-control
  loureiroImpact
  ("field" ∷ "seniority" ∷ "role criticality" ∷ "programme maturity" ∷ "institution" ∷ "time period" ∷ [])
  "matched ordinary departures across each roster member's technical peer population"
  "normalized disruption impact across milestone, replacement, knowledge-transfer, reorganisation and performance axes"
  "same temporal window per matched stratum"
  "feature scoring and control selection must be fixed before observing case/control impact labels"

------------------------------------------------------------------------
-- Acquisition frontier.
------------------------------------------------------------------------

data ImpactAcquisitionPriority : Set where
  immediateImpactSearch
  secondaryImpactSearch
  : ImpactAcquisitionPriority

record ImpactAcquisitionTarget : Set where
  constructor impact-acquisition-target
  field
    priority : ImpactAcquisitionPriority
    target : String
    preferredEvidence : String
    discriminatoryValue : String

open ImpactAcquisitionTarget public

successionAndReplacementTarget : ImpactAcquisitionTarget
successionAndReplacementTarget = impact-acquisition-target
  immediateImpactSearch
  "succession / replacement latency"
  "job postings, successor appointments, team rosters, archived org charts, project biographies, programme updates"
  "directly tests low-replaceability rather than inferring it from prestige or tenure"

milestoneTarget : ImpactAcquisitionTarget
milestoneTarget = impact-acquisition-target
  immediateImpactSearch
  "pre/post technical milestones"
  "roadmaps, schedules, review presentations, annual reports, deliverables, launch/test dates, funding milestones"
  "tests whether the loss generated measurable programme friction or delay"

knowledgeTransferTarget : ImpactAcquisitionTarget
knowledgeTransferTarget = impact-acquisition-target
  secondaryImpactSearch
  "knowledge-transfer / unique-qualification gap"
  "role descriptions, institutional tributes describing unique duties, handover records, successor interviews, technical-team testimony"
  "distinguishes publicly documented knowledge from difficult-to-replace tacit implementation knowledge"

record CurrentImpactAssessment : Set where
  constructor current-impact-assessment
  field
    keyPersonImpactEstablishedForRoster : Bool
    keyPersonImpactEstablishedForRosterIsFalse :
      keyPersonImpactEstablishedForRoster ≡ false
    impactCanBeInvestigatedWithoutActorTheory : Bool
    impactCanBeInvestigatedWithoutActorTheoryIsTrue :
      impactCanBeInvestigatedWithoutActorTheory ≡ true
    ordinaryMatchedImpactWouldWeakenKeyPersonSelection : Bool
    ordinaryMatchedImpactWouldWeakenKeyPersonSelectionIsTrue :
      ordinaryMatchedImpactWouldWeakenKeyPersonSelection ≡ true

canonicalCurrentImpactAssessment : CurrentImpactAssessment
canonicalCurrentImpactAssessment = current-impact-assessment
  false refl
  true refl
  true refl
