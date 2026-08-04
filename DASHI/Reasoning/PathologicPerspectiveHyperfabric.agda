module DASHI.Reasoning.PathologicPerspectiveHyperfabric where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Foundations.StageAtlasZeroToTwelve as Stage
import DASHI.Reasoning.PathologicConstraintSystem as Constraint
import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric

------------------------------------------------------------------------
-- Source calibration:
--
-- * Matthew Kendall, "Reading Pathologic 2: Russian Literature as a
--   Trans-Medial Idea", Russian Literature 138-139 (2023),
--   DOI 10.1016/j.ruslit.2022.11.004.
-- * Marie Beckmann, "Posthuman tragedy on the virtual stage in Pathologic 2",
--   International Journal of Performance Arts and Digital Media 21(3), 2025,
--   DOI 10.1080/14794713.2025.2555035.
--
-- The three routes are local epistemic sections over one event field.  A
-- player may retain cross-run knowledge unavailable to the currently enacted
-- character.  No canonical view-from-nowhere is supplied.
------------------------------------------------------------------------

data WorldQuestion : Set where
  plagueCause polyhedronValue townValue routeCost murdererIdentity : WorldQuestion

data PerspectiveEvidence :
    Constraint.Doctor → WorldQuestion → Set where
  bachelorPolyhedronTranscendence :
    PerspectiveEvidence Constraint.bachelor polyhedronValue
  bachelorTownAsLostCause :
    PerspectiveEvidence Constraint.bachelor townValue
  haruspexEarthWound :
    PerspectiveEvidence Constraint.haruspex plagueCause
  haruspexTownOrganism :
    PerspectiveEvidence Constraint.haruspex townValue
  changelingJointPreservation :
    PerspectiveEvidence Constraint.changeling polyhedronValue
  changelingSacrificeLogic :
    PerspectiveEvidence Constraint.changeling routeCost

record PerspectiveWitness
    (doctor : Constraint.Doctor)
    (question : WorldQuestion) : Set where
  field
    evidence : PerspectiveEvidence doctor question
    claimLabel : String
    sourceReceipt : String
    interpretationCandidateOnly : Bool

open PerspectiveWitness public

------------------------------------------------------------------------
-- Typed perspective hyperfabric: a doctor is incident to a question only
-- when a route-specific evidence constructor exists.
------------------------------------------------------------------------

questionStalk : WorldQuestion → Set
questionStalk question = ⊤

doctorStalk : Constraint.Doctor → Set
doctorStalk doctor = ⊤

perspectiveRestrict :
  ∀ {doctor question} →
  PerspectiveEvidence doctor question →
  doctorStalk doctor →
  questionStalk question
perspectiveRestrict evidence tt = tt

questionProvenance : WorldQuestion → List String
questionProvenance plagueCause =
  "route-indexed plague-cause evidence" ∷ []
questionProvenance polyhedronValue =
  "Bachelor, Haruspex and Changeling valuation conflict" ∷ []
questionProvenance townValue =
  "route-indexed town ontology and preservation claim" ∷ []
questionProvenance routeCost =
  "resource, sacrifice and ending dependency" ∷ []
questionProvenance murdererIdentity =
  "asymmetric hearsay, access and investigation" ∷ []

questionSalience : WorldQuestion → Nat
questionSalience plagueCause = 3
questionSalience polyhedronValue = 3
questionSalience townValue = 3
questionSalience routeCost = 3
questionSalience murdererIdentity = 2

canonicalPerspectiveHyperfabric :
  Hyperfabric.TypedHyperfabric Constraint.Doctor WorldQuestion
canonicalPerspectiveHyperfabric = record
  { vertexStalk = doctorStalk
  ; edgeStalk = questionStalk
  ; incidence = PerspectiveEvidence
  ; restrict = perspectiveRestrict
  ; edgeProvenance = questionProvenance
  ; edgeSalience = questionSalience
  ; fabricLabel = "Pathologic route-indexed epistemic hyperfabric"
  }

------------------------------------------------------------------------
-- Player/character/developer knowledge layers.
------------------------------------------------------------------------

data KnowledgeLayer : Set where
  characterLayer : Constraint.Doctor → KnowledgeLayer
  playerLayer developerLayer : KnowledgeLayer

data Knows : KnowledgeLayer → WorldQuestion → Set where
  characterKnowsFromRoute :
    ∀ {doctor question} →
    PerspectiveEvidence doctor question →
    Knows (characterLayer doctor) question
  playerCrossRunKnowledge :
    ∀ {question} →
    Knows playerLayer question
  developerConstructionKnowledge :
    ∀ {question} →
    Knows developerLayer question

record PolytemporalKnowledge : Set where
  field
    currentDoctor : Constraint.Doctor
    priorRuns : List Constraint.Doctor
    playerQuestion : WorldQuestion
    playerKnows : Knows playerLayer playerQuestion
    characterKnowledgeAvailable : Bool
    playerMaySelectCharacterSpeech : Bool
    characterAutomaticallyOwnsPlayerKnowledge : Bool
    knowledgeReceipt : String

------------------------------------------------------------------------
-- Incomparable endings without a hidden scalar objective.
------------------------------------------------------------------------

data EndingProposal : Set where
  bachelorProposal haruspexProposal changelingProposal : EndingProposal

data PreservationTarget : Set where
  preserveTown preservePolyhedron preserveBoth : PreservationTarget

data Preserves : EndingProposal → PreservationTarget → Set where
  bachelorPreservesPolyhedron : Preserves bachelorProposal preservePolyhedron
  haruspexPreservesTown : Preserves haruspexProposal preserveTown
  changelingPreservesBoth : Preserves changelingProposal preserveBoth

data EndingCost : Set where
  townDestroyed polyhedronDestroyed consentingSacrifice : EndingCost

data PaysCost : EndingProposal → EndingCost → Set where
  bachelorPaysTownCost : PaysCost bachelorProposal townDestroyed
  haruspexPaysPolyhedronCost : PaysCost haruspexProposal polyhedronDestroyed
  changelingPaysSacrificeCost : PaysCost changelingProposal consentingSacrifice

data ViewFromNowhere : Set where

noCanonicalViewFromNowhere : ¬ ViewFromNowhere
noCanonicalViewFromNowhere ()

record EndingParallax : Set where
  field
    bachelorHaruspexComparison : PNF.ComparisonResult
    comparisonIsNoTypedMeet :
      bachelorHaruspexComparison ≡ PNF.noTypedMeet
    bachelorPreservation : Preserves bachelorProposal preservePolyhedron
    haruspexPreservation : Preserves haruspexProposal preserveTown
    noDeclaredScalarUtility : Bool
    synthesisRequiresAdditionalValueJudgment : Bool

canonicalEndingParallax : EndingParallax
canonicalEndingParallax = record
  { bachelorHaruspexComparison = PNF.noTypedMeet
  ; comparisonIsNoTypedMeet = refl
  ; bachelorPreservation = bachelorPreservesPolyhedron
  ; haruspexPreservation = haruspexPreservesTown
  ; noDeclaredScalarUtility = true
  ; synthesisRequiresAdditionalValueJudgment = true
  }

------------------------------------------------------------------------
-- Independent twelve-day/stage lens.  Index equality does not identify game
-- days with the repository's philosophical stage readings.
------------------------------------------------------------------------

data PathologicDay : Set where
  prologue day-1 day-2 day-3 day-4 day-5 day-6 : PathologicDay
  day-7 day-8 day-9 day-10 day-11 day-12 : PathologicDay

dayToStage : PathologicDay → Stage.StageAtlasZeroToTwelve
dayToStage prologue = Stage.stage-0
dayToStage day-1 = Stage.stage-1
dayToStage day-2 = Stage.stage-2
dayToStage day-3 = Stage.stage-3
dayToStage day-4 = Stage.stage-4
dayToStage day-5 = Stage.stage-5
dayToStage day-6 = Stage.stage-6
dayToStage day-7 = Stage.stage-7
dayToStage day-8 = Stage.stage-8
dayToStage day-9 = Stage.stage-9
dayToStage day-10 = Stage.stage-10
dayToStage day-11 = Stage.stage-11
dayToStage day-12 = Stage.stage-12

day12MapsToStage12 :
  dayToStage day-12 ≡ Stage.stage-12
day12MapsToStage12 = refl

record PathologicPerspectiveAuthorityBoundary : Set where
  field
    routeEvidenceIndexed : Bool
    playerCharacterKnowledgeSeparated : Bool
    developerKnowledgeSeparated : Bool
    canonicalViewFromNowhereProvided : Bool
    endingComparisonHasDeclaredScalarUtility : Bool
    dayNumberCreatesStageSemantics : Bool
    routePerspectiveProvesWorldOntology : Bool
    boundaryNote : String

canonicalPathologicPerspectiveAuthorityBoundary :
  PathologicPerspectiveAuthorityBoundary
canonicalPathologicPerspectiveAuthorityBoundary = record
  { routeEvidenceIndexed = true
  ; playerCharacterKnowledgeSeparated = true
  ; developerKnowledgeSeparated = true
  ; canonicalViewFromNowhereProvided = false
  ; endingComparisonHasDeclaredScalarUtility = false
  ; dayNumberCreatesStageSemantics = false
  ; routePerspectiveProvesWorldOntology = false
  ; boundaryNote =
      "The three routes are typed local sections with asymmetric access. Cross-run player knowledge and developer provenance do not collapse into character knowledge or a neutral totalisation."
  }
