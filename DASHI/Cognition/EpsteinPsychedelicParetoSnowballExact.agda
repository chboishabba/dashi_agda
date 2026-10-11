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
  DoblinPublicBenefitGovernance true true true true 1 4
  "Acquire Doblin/MAPS public-benefit/private-profit governance claims with author-self-report attribution separated from independent verification."

chomskyCell : Pareto.RequirementCandidate AcquisitionRequirement
chomskyCell = Pareto.requirement-candidate
  ChomskyLanguageAIDispute true true true true 3 4
  "Resolve Chomsky corpus mention and cross-pollinate existing Manufacturing Consent prior art with AI-era evidence on poverty of stimulus and linguistic competence without promoting mention to relationship or model performance to human mechanism."

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
  scopolamineCell ∷ hearstCell ∷ adjacentBatesCell ∷ broadMAPSCell ∷ []

-- At the current calibration Gino Yu saturation dominates every other live
-- acquisition cell. After that corpus is paid, recompute rather than assuming
-- the present ordering persists.
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
  "Saturate Gino Yu first: enumerate every Epstein/Yu email, participant, venue, substance, funding request, introduction and attachment; bind each claim to EFTA identity."
  "Recompute frontier, then resolve Doblin/MAPS intersection and every proposed/actual contact edge without promoting invitation lists to meetings; keep Doblin governance claims source-attributed."
  "Recompute again, then test scopolamine/trumpet same-object joins, Hearst/PSFC/MAPS chronology and Chomsky corpus/language-AI intersections; keep administration, relationship and direct-funding claims open absent receipts."
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
