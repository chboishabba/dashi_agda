module DASHI.Cognition.CognitiveWarfarePlatoTraumaDetectorWeldExact where

------------------------------------------------------------------------
-- COGNITIVE-WARFARE / PLATO-CAVE / TRAUMA-MEMORY DETECTOR WELD
--
-- This owner composes existing theorem surfaces.  It does not diagnose any
-- person, campaign or actor.
--
-- The detector is intentionally vector-valued:
--
--   content
--   x observer/action-cone deformation
--   x provenance
--
-- The finite model proves independence obligations:
--
--   same content can have different provenance;
--   same provenance can have different cone deformation;
--   same cone deformation can have different provenance.
--
-- Therefore:
--
--   deformation != hostile influence
--   provenance != truth
--   content equality != common controller
--
-- Provenance remains a source-native refinement coordinate when the declared
-- consumer actually asks about origin.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Product using (_×_; _,_; proj₂)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.ResourceIndexedObserverRefinementExact as Resource
import DASHI.Cognition.CognitiveWarfareAdmissibleDetectionExact as Detection
import DASHI.Cognition.PlatoCaveTraumaMemoryDecisionBridgeExact as Cave
import DASHI.Biology.ObserverRelativeReachableSubfabricExact as Reach
import DASHI.Biology.EmbodiedCausalConeFeedbackExact as Cone
import DASHI.Cognition.PNF.TrialecticMemoryLearningHyperfabricExact as Trialectic
import DASHI.Cognition.PNF.MemoryCommandSeparationExact as MemoryCommand
import DASHI.Cognition.CaveTraumaNonErasingReopeningExact as Reopening

------------------------------------------------------------------------
-- Finite product-observer carrier.
------------------------------------------------------------------------

data NarrativeContent : Set where
  sameNarrativeContent : NarrativeContent

data ConeClass : Set where
  broadCone : ConeClass
  contractedCone : ConeClass

data DetectorState : Set where
  organicBroad : DetectorState
  organicContracted : DetectorState
  influenceBroad : DetectorState
  influenceContracted : DetectorState

content : DetectorState → NarrativeContent
content _ = sameNarrativeContent

coneClass : DetectorState → ConeClass
coneClass organicBroad = broadCone
coneClass organicContracted = contractedCone
coneClass influenceBroad = broadCone
coneClass influenceContracted = contractedCone

provenance : DetectorState → Detection.Origin
provenance organicBroad = Detection.organicOrigin
provenance organicContracted = Detection.organicOrigin
provenance influenceBroad = Detection.influenceOrigin
provenance influenceContracted = Detection.influenceOrigin

contentConeObserver :
  DetectorState → NarrativeContent × ConeClass
contentConeObserver state =
  content state , coneClass state

fullDetectorObserver :
  DetectorState →
  (NarrativeContent × ConeClass) × Detection.Origin
fullDetectorObserver state =
  contentConeObserver state , provenance state

------------------------------------------------------------------------
-- Axis independence.
------------------------------------------------------------------------

sameContentDifferentProvenance :
  content organicBroad ≡ content influenceBroad
  ×
  (provenance organicBroad ≡ provenance influenceBroad → ⊥)
sameContentDifferentProvenance =
  refl , Detection.organicOriginNotInfluence

sameProvenanceDifferentCone :
  provenance organicBroad ≡ provenance organicContracted
  ×
  (coneClass organicBroad ≡ coneClass organicContracted → ⊥)
sameProvenanceDifferentCone =
  refl , λ ()

sameConeDifferentProvenance :
  coneClass organicContracted ≡ coneClass influenceContracted
  ×
  (provenance organicContracted ≡ provenance influenceContracted → ⊥)
sameConeDifferentProvenance =
  refl , Detection.organicOriginNotInfluence

------------------------------------------------------------------------
-- Query-indexing: the same surface can be adequate for cone state while
-- inadequate for provenance.
------------------------------------------------------------------------

contentConeDeterminesConeClass :
  NF.FactorsThrough contentConeObserver coneClass
contentConeDeterminesConeClass =
  NF.factorsThrough
    proj₂
    (λ state → refl)

fullDetectorDeterminesProvenance :
  NF.FactorsThrough fullDetectorObserver provenance
fullDetectorDeterminesProvenance =
  NF.factorsThrough
    proj₂
    (λ state → refl)

------------------------------------------------------------------------
-- Content + deformation still cannot answer the provenance query.
------------------------------------------------------------------------

contentConeCannotDetermineProvenance :
  NF.FactorsThrough contentConeObserver provenance → ⊥
contentConeCannotDetermineProvenance =
  NF.witnessRulesOutEveryFlatFactorisation witness
  where
    witness :
      NF.NonFactorabilityWitness contentConeObserver provenance
    witness =
      NF.nonFactorabilityWitness
        organicContracted
        influenceContracted
        refl
        Detection.organicOriginNotInfluence

------------------------------------------------------------------------
-- Adding provenance is a genuine strict refinement for this consumer.
------------------------------------------------------------------------

fullDetectorStrictlyRefinesContentCone :
  Observer.StrictRefinement
    contentConeObserver
    (Observer.pairObserver contentConeObserver provenance)
fullDetectorStrictlyRefinesContentCone =
  Observer.strictPairRefinement
    contentConeObserver
    provenance
    organicContracted
    influenceContracted
    refl
    Detection.organicOriginNotInfluence

------------------------------------------------------------------------
-- Existing cave / trauma / decision theorems retained as exact donor surfaces.
------------------------------------------------------------------------

shadowIsNotFalsehood :
  Cave.ShadowEqualsFalsehood → ⊥
shadowIsNotFalsehood =
  Cave.shadowDoesNotMeanFalse

learnedThreatDoesNotProveThreatTruth :
  Trialectic.ThreatSensitivityImpliesThreatTruth → ⊥
learnedThreatDoesNotProveThreatTruth =
  Trialectic.threatSensitivityDoesNotEstablishThreatTruth

learnedHistoryCanChangeGate :
  Cone.gate Cone.baselineLaw Cone.approachSafety
  ≡ Cone.gate Cone.learnedThreatLaw Cone.approachSafety →
  ⊥
learnedHistoryCanChangeGate =
  Cave.learnedHistoryCanDeformTransitionGateWithoutDeletingCarrier

sameWorldCanChangeAccessibleCone :
  Reach.live Reach.worldLayer Reach.regulatedContext Reach.flexiblePlanning
  ≡ Reach.live Reach.worldLayer Reach.mobilisedContext Reach.flexiblePlanning
  ×
  (Reach.live Reach.accessibleLayer Reach.regulatedContext Reach.flexiblePlanning
   ≡ Reach.live Reach.accessibleLayer Reach.mobilisedContext Reach.flexiblePlanning
   → ⊥)
sameWorldCanChangeAccessibleCone =
  Cave.sameWorldCanHaveDifferentAccessiblePlanning

memoryPreservingCommandRevision :
  ∀ memory →
  MemoryCommand.MemoryCommandSeparationWitness memory
memoryPreservingCommandRevision =
  Cave.memoryCanBePreservedWhileCommandChanges

nonErasingCorrectiveReopening :
  ∀ memory →
  Reopening.NonErasingCorrectiveReopening memory
nonErasingCorrectiveReopening =
  Reopening.canonicalNonErasingCorrectiveReopening

------------------------------------------------------------------------
-- Resource-indexed refinement.
--
-- The provenance-enriched detector is structurally better for the provenance
-- consumer, but that does not imply it fits the currently declared budget.
------------------------------------------------------------------------

contentConeCost : Nat
contentConeCost = 2

fullDetectorCost : Nat
fullDetectorCost = 3

detectorBudget : Nat
detectorBudget = 2

contentConeWithinBudget :
  Resource.WithinBudget detectorBudget contentConeCost
contentConeWithinBudget =
  s≤s (s≤s z≤n)

fullDetectorOutsideBudget :
  Resource.WithinBudget detectorBudget fullDetectorCost → ⊥
fullDetectorOutsideBudget ()

provenanceRefinementMayExceedBudget :
  Resource.RefinementBudgetFailure
    contentConeObserver
    fullDetectorObserver
provenanceRefinementMayExceedBudget =
  Resource.refinement-budget-failure
    fullDetectorStrictlyRefinesContentCone
    detectorBudget
    contentConeCost
    fullDetectorCost
    contentConeWithinBudget
    fullDetectorOutsideBudget

------------------------------------------------------------------------
-- No-promotion permissions.
------------------------------------------------------------------------

data ConeDeformationImpliesInfluence : Set where

coneDeformationDoesNotEstablishInfluence :
  ConeDeformationImpliesInfluence → ⊥
coneDeformationDoesNotEstablishInfluence ()

data ProvenanceImpliesTruth : Set where

provenanceDoesNotEstablishTruth :
  ProvenanceImpliesTruth → ⊥
provenanceDoesNotEstablishTruth ()

data ContentEqualityImpliesCommonController : Set where

contentEqualityDoesNotEstablishCommonController :
  ContentEqualityImpliesCommonController → ⊥
contentEqualityDoesNotEstablishCommonController ()

data CoherenceImpliesTruth : Set where

coherenceDoesNotEstablishTruth :
  CoherenceImpliesTruth → ⊥
coherenceDoesNotEstablishTruth ()

------------------------------------------------------------------------
-- Detector interpretation.
--
-- A useful detector may retain all three coordinates, but authority is
-- query-indexed.  Cone deformation is evidence about changed effective
-- reachability; provenance is evidence about origin; neither is silently
-- promoted to content truth or hostile intent.
------------------------------------------------------------------------

record CognitiveDetectorWeldBoundary : Set where
  constructor cognitive-detector-weld-boundary
  field
    contentDeterminesProvenance : Bool
    coneDeformationDeterminesProvenance : Bool
    provenanceDeterminesConeDeformation : Bool
    contentAndConeDetermineProvenance : Bool
    addingProvenanceCanStrictlyRefine : Bool
    coneDeformationImpliesHostileInfluence : Bool
    provenanceImpliesTruth : Bool
    coherenceImpliesTruth : Bool

canonicalCognitiveDetectorWeldBoundary :
  CognitiveDetectorWeldBoundary
canonicalCognitiveDetectorWeldBoundary =
  cognitive-detector-weld-boundary
    false false false false true false false false
