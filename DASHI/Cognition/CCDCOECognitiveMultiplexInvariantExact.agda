module DASHI.Cognition.CCDCOECognitiveMultiplexInvariantExact where

------------------------------------------------------------------------
-- CCDCOE 2026 STRUCTURE-CENTRIC COGNITIVE-VULNERABILITY CASE
--
-- Source: Korobeynikov, Davydiuk and Mokhor (2026),
-- "Ontological Foundations of Cognitive Warfare", NATO CCDCOE.
--
-- This is a finite, source-attributed mathematical interpretation.
-- It does NOT certify the article's causal hypotheses, infer a hostile
-- actor, classify any person, or represent a measured human network.
-- The authors explicitly leave empirical connectivity/coherence metrics
-- and connector-node identification to future work.
--
-- Reuse: source attribution, non-factorability, observer/provenance,
-- and cognitive detector non-promotion are owned by existing modules.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Cognition.CognitiveWarfareAdmissibleDetectionExact as Detection
import DASHI.Cognition.CognitiveWarfarePlatoTraumaDetectorWeldExact as Detector

ccdcoe2026Source : Source.AttributedSource
ccdcoe2026Source =
  Source.mkNoDOISource
    "Fedir Korobeynikov; Andrii Davydiuk; Volodymyr Mokhor"
    "Ontological Foundations of Cognitive Warfare"
    "NATO Cooperative Cyber Defence Centre of Excellence, Tallinn"
    "2026"
    "https://ccdcoe.org/uploads/2026/04/ONTOLOGICAL_FOUNDATIONS_OF_COGNITIVE_WARFARE.pdf"
    Source.institutionalSource
    "Conceptual source for five invariant layers and their multiplex coupling; not an empirical proof or NATO policy statement"
    Source.publicAttribution

------------------------------------------------------------------------
-- One common actor carrier across five distinct invariant layers.
-- The source's five classes are preserved; these are not five agents.
------------------------------------------------------------------------

data Actor : Set where
  agentA : Actor
  agentB : Actor

data InvariantLayer : Set where
  epistemic : InvariantLayer
  axiological : InvariantLayer
  identificatory : InvariantLayer
  social : InvariantLayer
  teleological : InvariantLayer

data Connector : Set where
  epistemicAxiological : Connector
  axiologicalIdentificatory : Connector
  identificatorySocial : Connector
  socialTeleological : Connector

data Architecture : Set where
  coupled : Architecture
  connectorLost : Architecture

-- A deliberately transparent finite specimen: each layer retains a
-- local relation among the SAME actors, independently of cross-layer
-- coupling. Not a claim that real institutions are complete graphs.
withinLayer : Architecture -> InvariantLayer -> Actor -> Actor -> Bool
withinLayer _ _ _ _ = true

localOperationPersists :
  (s : Architecture) -> (l : InvariantLayer) ->
  (a b : Actor) -> withinLayer s l a b ≡ true
localOperationPersists _ _ _ _ = refl

localOperationUnchangedByCut :
  (l : InvariantLayer) -> (a b : Actor) ->
  withinLayer coupled l a b ≡ withinLayer connectorLost l a b
localOperationUnchangedByCut _ _ _ = refl

-- Interlayer coupling is separately represented, for the same actors.
-- We deliberately lose ONE selected dependency, not a local layer.
coupling : Architecture -> Actor -> Connector -> Bool
coupling coupled _ _ = true
coupling connectorLost _ identificatorySocial = false
coupling connectorLost _ _ = true

andB : Bool -> Bool -> Bool
andB true b = b
andB false _ = false

-- Four links form a selected spanning path across all five invariants.
-- Other network topologies would require a distinct connectivity model.
chain : Bool -> Bool -> Bool -> Bool -> Bool
chain e a i s = andB e (andB a (andB i s))

integratedPath : Architecture -> Actor -> Bool
integratedPath graph actor =
  chain (coupling graph actor epistemicAxiological)
        (coupling graph actor axiologicalIdentificatory)
        (coupling graph actor identificatorySocial)
        (coupling graph actor socialTeleological)

intactPath :
  (actor : Actor) -> integratedPath coupled actor ≡ true
intactPath _ = refl

singleCutBlocksPath :
  (first second fourth : Bool) ->
  chain first second false fourth ≡ false
singleCutBlocksPath false _ _ = refl
singleCutBlocksPath true false _ = refl
singleCutBlocksPath true true _ = refl

connectorCutBlocksSelectedPath :
  (actor : Actor) -> integratedPath connectorLost actor ≡ false
connectorCutBlocksSelectedPath actor =
  singleCutBlocksPath true true true

-- The central source-bounded counterexample:
-- all local layers work, yet selected global coordination fails.
structuralDecoherenceWitness :
  (l : InvariantLayer) -> (a b : Actor) ->
  withinLayer connectorLost l a b ≡ true
structuralDecoherenceWitness = localOperationPersists connectorLost

------------------------------------------------------------------------
-- Observer-relative invisibility: current outward functionality can
-- conceal this particular interlayer cut. Not universal undetectability.
------------------------------------------------------------------------

data OutwardReport : Set where
  componentsStillFunction : OutwardReport

outward : Architecture -> OutwardReport
outward _ = componentsStillFunction

pathOutcomesDiffer :
  integratedPath coupled agentA ≡
  integratedPath connectorLost agentA -> ⊥
pathOutcomesDiffer ()

outwardDoesNotDetermineIntegratedPath :
  NF.FactorsThrough outward (λ s -> integratedPath s agentA) -> ⊥
outwardDoesNotDetermineIntegratedPath =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      coupled connectorLost refl pathOutcomesDiffer)

------------------------------------------------------------------------
-- Even knowing the complete specimen's architecture does not determine
-- whether an externally originating influence was involved.
-- This reuses the already-owned provenance distinction.
------------------------------------------------------------------------

data Episode : Set where
  organicCoupled : Episode
  organicCut : Episode
  influenceCoupled : Episode
  influenceCut : Episode

episodeArchitecture : Episode -> Architecture
episodeArchitecture organicCoupled = coupled
episodeArchitecture organicCut = connectorLost
episodeArchitecture influenceCoupled = coupled
episodeArchitecture influenceCut = connectorLost

episodeOrigin : Episode -> Detection.Origin
episodeOrigin organicCoupled = Detection.organicOrigin
episodeOrigin organicCut = Detection.organicOrigin
episodeOrigin influenceCoupled = Detection.influenceOrigin
episodeOrigin influenceCut = Detection.influenceOrigin

architectureDoesNotDetermineOrigin :
  NF.FactorsThrough episodeArchitecture episodeOrigin -> ⊥
architectureDoesNotDetermineOrigin =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      organicCut influenceCut refl
      Detection.organicOriginNotInfluence)

structureDiffers : coupled ≡ connectorLost -> ⊥
structureDiffers ()

originDoesNotDetermineArchitecture :
  NF.FactorsThrough episodeOrigin episodeArchitecture -> ⊥
originDoesNotDetermineArchitecture =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      organicCoupled organicCut refl structureDiffers)

-- Coherence, provenance, and present target observation are different
-- questions, as established by the existing cognition owner.
coherenceCannotProveTruth :
  Detector.CoherenceImpliesTruth -> ⊥
coherenceCannotProveTruth =
  Detector.coherenceDoesNotEstablishTruth

------------------------------------------------------------------------
-- Symbolic repair is allowed at the structural level. No proof here
-- that a feasible, safe, consentful or measured intervention exists.
------------------------------------------------------------------------

abstractRepair : Architecture -> Architecture
abstractRepair _ = coupled

repairRestoresSelectedPath :
  (s : Architecture) -> (actor : Actor) ->
  integratedPath (abstractRepair s) actor ≡ true
repairRestoresSelectedPath _ _ = refl

record EmpiricalAndAttributionBoundary : Set where
  constructor empirical-and-attribution-boundary
  field
    finiteWitnessIsEmpiricalMeasurement : Bool
    connectivityLossAloneProvesHostileIntent : Bool
    coherenceAloneProvesTruth : Bool
    paperIsBindingNATOPolicy : Bool
    universalUndetectabilityEstablished : Bool
    abstractRepairIsValidatedIntervention : Bool

canonicalEmpiricalAndAttributionBoundary :
  EmpiricalAndAttributionBoundary
canonicalEmpiricalAndAttributionBoundary =
  empirical-and-attribution-boundary
    false false false false false false
