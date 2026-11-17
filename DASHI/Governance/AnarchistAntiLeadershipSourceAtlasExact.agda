module DASHI.Governance.AnarchistAntiLeadershipSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.OccupyConsensusEvidenceAtlasExact as Occupy

------------------------------------------------------------------------
-- ANARCHIST / HORIZONTAL ORGANISING AND LEADERSHIP-TENSION SOURCE ATLAS
--
-- Source propositions remain source-owned. DASHI owns only the typed source
-- roles and non-collapse boundaries below.
--
-- The atlas deliberately retains BOTH classical poles:
--   * Freeman: informal / unacknowledged structure can hide power and elites;
--   * Levine: formal hierarchy can itself legitimate and reproduce domination.
-- The current literature does not dissolve that tension. It instead gives a
-- richer vocabulary for distributed coordination, emergent/informal influence,
-- rotating expertise, autonomy and anti-leadership dynamics.
------------------------------------------------------------------------

data LeadershipEvidenceRole : Set where
  structurelessnessCritique : LeadershipEvidenceRole
  formalHierarchyCritique : LeadershipEvidenceRole
  horizontalCoordinationObservation : LeadershipEvidenceRole
  leaderlessnessCriticalSynthesis : LeadershipEvidenceRole
  distributedCoordinationTheory : LeadershipEvidenceRole

record LeadershipSource : Set where
  constructor leadership-source
  field
    author : String
    title : String
    venue : String
    year : Nat
    identifier : String
    role : LeadershipEvidenceRole
    sourceSupports : String
    sourceDoesNotByItselfSupport : String

open LeadershipSource public

freemanStructurelessness : LeadershipSource
freemanStructurelessness =
  leadership-source
    "Jo Freeman"
    "The Tyranny of Structurelessness"
    "women's-liberation / Berkeley Journal of Sociology publication lineage"
    1972
    "historical essay; versions circulated 1970-1973"
    structurelessnessCritique
    "the organisational critique that informal or unacknowledged structures can concentrate power while avoiding explicit accountability"
    "a theorem that every formal hierarchy is democratic, non-dominating or desirable"

levineTyrannyOfTyranny : LeadershipSource
levineTyrannyOfTyranny =
  leadership-source
    "Cathy Levine"
    "The Tyranny of Tyranny"
    "Black Rose, no. 1"
    1974
    "historical anarchist-feminist response"
    formalHierarchyCritique
    "the counter-critique that formalisation and explicit hierarchy can legitimate authority and reproduce domination rather than automatically curing it"
    "a theorem that informality or structurelessness eliminates power relations"

keshtibanCallahanHarris : LeadershipSource
keshtibanCallahanHarris =
  leadership-source
    "Amir E. Keshtiban; Jamie L. Callahan; Martin Harris"
    "Leaderlessness in social movements: Advancing space, symbols, and spectacle as modes of leadership"
    "Human Resource Development Quarterly"
    2021
    "doi:10.1002/hrdq.21460"
    horizontalCoordinationObservation
    "analysis of Occupy London showing coordination can be accomplished horizontally without conventional formal leadership or authority structures"
    "a claim that influence, power or leadership functions disappear in horizontal movements"

caruso2024 : LeadershipSource
caruso2024 =
  leadership-source
    "Giuseppe Caruso"
    "The leaderlessness conundrum: Politics and anti-politics in global justice movements"
    "Leadership 20(6):337-357"
    2024
    "doi:10.1177/17427150241272871"
    leaderlessnessCriticalSynthesis
    "a critical synthesis in which global-justice and Occupy-style movements reject dominant bureaucratic/charismatic leadership while leadership relations and informal structures can remain present"
    "a universal causal law, a proof that leaderlessness fails, or a proof that concentrated leadership is necessary"

fouladi2025 : LeadershipSource
fouladi2025 =
  leadership-source
    "Farzaneh Fouladi"
    "The Paradox of Anti-Leadership Movements: Understanding Coordination Without Authority"
    "Academy of Management Proceedings 2025"
    2025
    "doi:10.5465/AMPROC.2025.20101poster"
    distributedCoordinationTheory
    "a theoretical framework proposing shared mental models, reframed informal power and rotating situation-specific expertise as coordination mechanisms in anti-leadership movements"
    "empirical validation of those mechanisms, a unique organisational optimum, or proof that rotating expertise eliminates domination"

canonicalLeadershipSources : List LeadershipSource
canonicalLeadershipSources =
  freemanStructurelessness
  ∷ levineTyrannyOfTyranny
  ∷ keshtibanCallahanHarris
  ∷ caruso2024
  ∷ fouladi2025
  ∷ []

-- Existing Occupy evidence remains an independently owned source atlas. This
-- anchor prevents the new SOTA layer from replacing the already plural
-- burden/benefit/coordination/adaptation evidence.
occupyEvidenceAnchor : Occupy.OccupyConsensusEvidenceBoundary
occupyEvidenceAnchor = Occupy.canonicalOccupyConsensusEvidenceBoundary

record AnarchistLeadershipSourceBoundary : Set where
  constructor anarchist-leadership-source-boundary
  field
    structurelessnessCritiquePresent : Bool
    formalHierarchyCritiquePresent : Bool
    occupyHorizontalCoordinationEvidencePresent : Bool
    recentLeaderlessnessCriticalSynthesisPresent : Bool
    sotaDistributedCoordinationPresent : Bool

    leaderlessMeansLeadershipless : Bool
    informalityMeansNoPower : Bool
    formalisationMeansNonDomination : Bool
    rotatingExpertiseMeansEqualVoice : Bool
    consensusMeansNonDomination : Bool
    theoryPaperCountsAsEmpiricalValidation : Bool
    anyOneSourceSettlesOrganisingDesign : Bool

open AnarchistLeadershipSourceBoundary public

canonicalAnarchistLeadershipSourceBoundary : AnarchistLeadershipSourceBoundary
canonicalAnarchistLeadershipSourceBoundary =
  anarchist-leadership-source-boundary
    true true true true true
    false false false false false false false

canonicalAnarchistLeadershipSourceReceipt : GenericReceipt.GenericReceipt
canonicalAnarchistLeadershipSourceReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "anarchist / horizontal leadership and organising tension atlas"
    "DASHI.Governance.AnarchistAntiLeadershipSourceAtlasExact"
    "canonicalAnarchistLeadershipSourceBoundary"
    "retains the Freeman/Levine structural tension, Occupy horizontal-coordination literature, Caruso's 2024 leaderlessness synthesis and Fouladi's 2025 theoretical distributed-coordination mechanisms as separately typed source roles"
    "leaderless is not leadershipless; informality does not erase power; formal hierarchy, rotating expertise or consensus do not by themselves establish non-domination; the 2025 theoretical framework is not empirical validation"
    "agda -i . DASHI/Governance/AnarchistLeadershipNonDominationTSFVRegression.agda"
