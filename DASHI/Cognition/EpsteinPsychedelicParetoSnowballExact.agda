module DASHI.Cognition.EpsteinPsychedelicParetoSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto

------------------------------------------------------------------------
-- PARETO / SNOWBALL ROUTER
--
-- Cost/gain are routing calibration only. They are not probabilities, truth
-- scores, culpability scores, or evidence grades. The frontier selects what to
-- acquire next; it never pays the requirement itself.
------------------------------------------------------------------------

data AcquisitionRequirement : Set where
  GinoYuCorpus : AcquisitionRequirement
  DoblinMAPSIntersection : AcquisitionRequirement
  DoblinPublicBenefitGovernance : AcquisitionRequirement
  ChomskyLanguageAIDispute : AcquisitionRequirement
  ChomskyEpsteinRelationship : AcquisitionRequirement
  BroaderSciencePatronageContext : AcquisitionRequirement
  BrainITGeometryContext : AcquisitionRequirement
  ScopolamineTrumpetSameObject : AcquisitionRequirement
  HearstFundingIntersection : AcquisitionRequirement
  AdjacentBatesThreadRecovery : AcquisitionRequirement
  BroadMAPSKeywordSweep : AcquisitionRequirement

ginoYuCell : Pareto.RequirementCandidate AcquisitionRequirement
ginoYuCell = Pareto.requirement-candidate
  GinoYuCorpus true true true true 1 9
  "Saturate Gino Yu correspondence: highest current split because direct funding, introductions, altered-state events, participants and venues co-occur in one primary lineage."

doblinMAPSCell : Pareto.RequirementCandidate AcquisitionRequirement
doblinMAPSCell = Pareto.requirement-candidate
  DoblinMAPSIntersection true true true true 2 7
  "Resolve every Doblin/MAPS occurrence and distinguish proposed invitation, meeting, correspondence, funding and later institutional overlap."

doblinGovernanceCell : Pareto.RequirementCandidate AcquisitionRequirement
doblinGovernanceCell = Pareto.requirement-candidate
  DoblinPublicBenefitGovernance true true true true 2 4
  "Acquire Doblin/MAPS public-benefit/private-profit governance claims with author-self-report attribution separated from institutional and external verification."

chomskyCell : Pareto.RequirementCandidate AcquisitionRequirement
chomskyCell = Pareto.requirement-candidate
  ChomskyLanguageAIDispute true true true true 4 4
  "Cross-pollinate Manufacturing Consent prior art with AI-era evidence on poverty of stimulus and linguistic competence; keep model performance distinct from human mechanism."

chomskyRelationshipCell : Pareto.RequirementCandidate AcquisitionRequirement
chomskyRelationshipCell = Pareto.requirement-candidate
  ChomskyEpsteinRelationship true true true true 3 5
  "Resolve direct Chomsky-Epstein correspondence, social contact, financial advice, introductions and project payments independently of Bach's weaker proposed-invite edge."

sciencePatronageCell : Pareto.RequirementCandidate AcquisitionRequirement
sciencePatronageCell = Pareto.requirement-candidate
  BroaderSciencePatronageContext true true true true 4 4
  "Situate the Yu/psychedelic lane inside the broader documented private-donor brokerage ecology without promoting patronage to scientific authority or universal network control."

brainITGeometryCell : Pareto.RequirementCandidate AcquisitionRequirement
brainITGeometryCell = Pareto.requirement-candidate
  BrainITGeometryContext true true true true 5 3
  "Use Brain-IT and representation-geometry work as modern methodological context only; do not back-project 2026 reconstruction capability into historical Epstein/Yu activity."

scopolamineCell : Pareto.RequirementCandidate AcquisitionRequirement
scopolamineCell = Pareto.requirement-candidate
  ScopolamineTrumpetSameObject true true true true 2 6
  "Recover adjacent context for EFTA00984429 and EFTA00865569 and test whether plant identity, possession, knowledge and use ever join on the same object."

hearstCell : Pareto.RequirementCandidate AcquisitionRequirement
hearstCell = Pareto.requirement-candidate
  HearstFundingIntersection true true true true 3 6
  "Resolve Epstein<->Hearst primary records against independently sourced Hearst/PSFC/MAPS funding chronology without importing causation."

adjacentBatesCell : Pareto.RequirementCandidate AcquisitionRequirement
adjacentBatesCell = Pareto.requirement-candidate
  AdjacentBatesThreadRecovery true true true true 3 5
  "Recover whole threads, attachments and adjacent Bates pages around the current seed documents."

broadMAPSCell : Pareto.RequirementCandidate AcquisitionRequirement
broadMAPSCell = Pareto.requirement-candidate
  BroadMAPSKeywordSweep true true true true 5 3
  "Broad MAPS keyword sweep after named-person and thread expansion; acronym/OCR noise makes it a lower-yield first move."

currentPortfolio : List (Pareto.RequirementCandidate AcquisitionRequirement)
currentPortfolio =
  ginoYuCell ∷ doblinMAPSCell ∷ doblinGovernanceCell ∷ chomskyCell ∷
  chomskyRelationshipCell ∷ sciencePatronageCell ∷ brainITGeometryCell ∷
  scopolamineCell ∷ hearstCell ∷ adjacentBatesCell ∷ broadMAPSCell ∷ []

-- The wider context changes interpretation but not the present acquisition
-- maximum: Gino Yu remains the cheapest/highest-gain primary-corpus seam.
currentFrontierExact :
  Pareto.paretoFrontier currentPortfolio ≡ ginoYuCell ∷ []
currentFrontierExact = refl

record CurrentEpsteinPsychedelicRoute : Set where
  constructor current-epstein-psychedelic-route
  field
    first : String
    secondAfterRecompute : String
    thirdAfterRecompute : String
    wholeThreadRequired : Bool
    attachmentsRequired : Bool
    adjacentBatesRequired : Bool
    broadKeywordSweepDeferred : Bool

currentEpsteinPsychedelicRoute : CurrentEpsteinPsychedelicRoute
currentEpsteinPsychedelicRoute = current-epstein-psychedelic-route
  "Saturate Gino Yu first: enumerate every Epstein/Yu email, participant, venue, substance, funding request, introduction, neurotechnology term and attachment; bind each claim to EFTA identity."
  "Recompute frontier, then resolve Doblin/MAPS actual-contact edges, Chomsky/Epstein direct-relationship chronology, and Hearst/PSFC/MAPS funding chronology without collapsing distinct relationships."
  "Then test scopolamine/trumpet same-object joins and adjacent Bates threads; retain broader science-patronage, Brain-IT and geometry work as contextual constraints unless a primary historical edge appears."
  true true true true

------------------------------------------------------------------------
-- ROUTING FIREWALLS.
------------------------------------------------------------------------

data ParetoRoutingCreatesTruth : Set where
data HighGainCreatesEvidenceGrade : Set where
data CorpusMultiplicityCreatesIndependentCorroboration : Set where
data SearchHitCreatesSameObjectIdentity : Set where

paretoRoutingCreatesTruth : Bool
paretoRoutingCreatesTruth = false

routingDoesNotCreateTruth : ParetoRoutingCreatesTruth → ⊥
routingDoesNotCreateTruth ()

highGainDoesNotCreateEvidenceGrade : HighGainCreatesEvidenceGrade → ⊥
highGainDoesNotCreateEvidenceGrade ()

multiplicityDoesNotCreateIndependence : CorpusMultiplicityCreatesIndependentCorroboration → ⊥
multiplicityDoesNotCreateIndependence ()

searchHitDoesNotCreateSameObject : SearchHitCreatesSameObjectIdentity → ⊥
searchHitDoesNotCreateSameObject ()
