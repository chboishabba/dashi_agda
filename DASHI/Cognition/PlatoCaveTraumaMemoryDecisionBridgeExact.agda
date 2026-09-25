module DASHI.Cognition.PlatoCaveTraumaMemoryDecisionBridgeExact where

------------------------------------------------------------------------
-- PLATO-CAVE / PARTIAL-OBSERVATION / MEMORY-LEARNING-DECISION BRIDGE
--
-- Plato's cave is used here only as a projection metaphor:
--
--   fine world/history -> presently available appearance ("shadow")
--
-- The formal content is DASHI-native.  No theorem below says that an
-- appearance is false, that a hidden state is "ultimate reality", or that
-- trauma determines belief, perception or action.
--
-- Cross-pollination:
--
--   lossy observer / FactorsThrough
--   -> collision fibre
--   -> source-native refinement
--   -> observer-relative reachable/actionable subfabric
--   -> learned-history deformation of transition law
--   -> memory != command
--   -> trauma/history != current decision
--   -> corrective evidence can reopen an observation fibre.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Biology.ObserverRelativeReachableSubfabricExact as Reach
import DASHI.Biology.EmbodiedCausalConeFeedbackExact as Cone
import DASHI.Biology.BodyModulatedDecisionCoordinatesExact as Controls
import DASHI.Cognition.PNF.AdmissibleFactorisationDecisionHyperfabricExact as Decision
import DASHI.Cognition.PNF.TrialecticMemoryLearningHyperfabricExact as Trialectic
import DASHI.Cognition.PNF.MemoryCommandSeparationExact as MemoryCommand

------------------------------------------------------------------------
-- Finite cave carrier: two fine situations cast the same current shadow.
------------------------------------------------------------------------

data FineCaveState : Set where
  objectAHidden : FineCaveState
  objectBHidden : FineCaveState
  objectARevealed : FineCaveState
  objectBRevealed : FineCaveState

data CaveAppearance : Set where
  commonShadow : CaveAppearance
  appearanceA : CaveAppearance
  appearanceB : CaveAppearance

shadowProjection : FineCaveState → CaveAppearance
shadowProjection objectAHidden = commonShadow
shadowProjection objectBHidden = commonShadow
shadowProjection objectARevealed = appearanceA
shadowProjection objectBRevealed = appearanceB

data FineIdentity : Set where
  identityA : FineIdentity
  identityB : FineIdentity

fineIdentity : FineCaveState → FineIdentity
fineIdentity objectAHidden = identityA
fineIdentity objectBHidden = identityB
fineIdentity objectARevealed = identityA
fineIdentity objectBRevealed = identityB

identityDiffers : identityA ≡ identityB → ⊥
identityDiffers ()

caveShadowCollision :
  NF.NonFactorabilityWitness shadowProjection fineIdentity
caveShadowCollision =
  NF.nonFactorabilityWitness
    objectAHidden
    objectBHidden
    refl
    identityDiffers

shadowCannotRecoverFineIdentity :
  NF.FactorsThrough shadowProjection fineIdentity → ⊥
shadowCannotRecoverFineIdentity =
  NF.witnessRulesOutEveryFlatFactorisation caveShadowCollision

------------------------------------------------------------------------
-- Merely recharting the same shadows cannot restore the erased distinction.
------------------------------------------------------------------------

shadowRechartCannotRecoverFineIdentity :
  ∀ {Recharted : Set} →
  (rechart : CaveAppearance → Recharted) →
  NF.FactorsThrough
    (λ state → rechart (shadowProjection state))
    fineIdentity →
  ⊥
shadowRechartCannotRecoverFineIdentity rechart =
  NF.rechartingCannotRecoverErasedPhenomenon
    rechart
    caveShadowCollision

------------------------------------------------------------------------
-- Adding a source-native fine coordinate is a genuine strict refinement.
------------------------------------------------------------------------

shadowPlusIdentityStrictlyRefinesShadow :
  Observer.StrictRefinement
    shadowProjection
    (Observer.pairObserver shadowProjection fineIdentity)
shadowPlusIdentityStrictlyRefinesShadow =
  Observer.strictPairRefinement
    shadowProjection
    fineIdentity
    objectAHidden
    objectBHidden
    refl
    identityDiffers

------------------------------------------------------------------------
-- The shadow itself is not typed as falsity.
------------------------------------------------------------------------

data ShadowEqualsFalsehood : Set where

shadowDoesNotMeanFalse :
  ShadowEqualsFalsehood → ⊥
shadowDoesNotMeanFalse ()

data RevealedCoordinateEqualsUltimateReality : Set where

refinementDoesNotClaimUltimateReality :
  RevealedCoordinateEqualsUltimateReality → ⊥
refinementDoesNotClaimUltimateReality ()

------------------------------------------------------------------------
-- Existing embodied/trauma-memory-learning results are the nontrivial cave
-- extension: observation is observer/body/history relative, and learning may
-- alter accessible/actionable futures without changing the world carrier.
------------------------------------------------------------------------

sameWorldCanHaveDifferentAccessiblePlanning :
  Reach.live Reach.worldLayer Reach.regulatedContext Reach.flexiblePlanning
  ≡ Reach.live Reach.worldLayer Reach.mobilisedContext Reach.flexiblePlanning
  ×
  (Reach.live Reach.accessibleLayer Reach.regulatedContext Reach.flexiblePlanning
   ≡ Reach.live Reach.accessibleLayer Reach.mobilisedContext Reach.flexiblePlanning
   → ⊥)
sameWorldCanHaveDifferentAccessiblePlanning =
  Reach.sameWorldDifferentBody Reach.flexiblePlanning
  ,
  Reach.sameWorldButBodyChangesAccessiblePlanning

learnedHistoryCanDeformTransitionGateWithoutDeletingCarrier :
  Cone.gate Cone.baselineLaw Cone.approachSafety
  ≡ Cone.gate Cone.learnedThreatLaw Cone.approachSafety →
  ⊥
learnedHistoryCanDeformTransitionGateWithoutDeletingCarrier =
  Cone.historyDeformationCanCloseApproachWithoutDeletingTransition

sameAccessDoesNotDetermineDecisionThreshold :
  Controls.sameAccessSurface Reach.regulatedContext
  ≡ Controls.sameAccessSurface Reach.mobilisedContext
  ×
  (Controls.decisionThreshold Controls.regulatedControls
   ≡ Controls.decisionThreshold Controls.mobilisedControls
   → ⊥)
sameAccessDoesNotDetermineDecisionThreshold =
  Controls.sameAccessDoesNotDetermineThreshold
  ,
  Controls.thresholdStillDiffers

traumaHistoryAloneDoesNotDetermineCurrentDecision :
  NF.FactorsThrough
    Decision.historyOnlyObserver
    Decision.currentDecisionConsumer →
  ⊥
traumaHistoryAloneDoesNotDetermineCurrentDecision =
  Decision.currentDecisionDoesNotFactorThroughTraumaHistoryAlone

threatSensitivityDoesNotEstablishThreatTruth :
  Trialectic.ThreatSensitivityImpliesThreatTruth → ⊥
threatSensitivityDoesNotEstablishThreatTruth =
  Trialectic.threatSensitivityDoesNotEstablishThreatTruth

------------------------------------------------------------------------
-- Memory may be retained while command/action weighting changes.
------------------------------------------------------------------------

memoryCanBePreservedWhileCommandChanges :
  ∀ memory →
  MemoryCommand.MemoryCommandSeparationWitness memory
memoryCanBePreservedWhileCommandChanges =
  MemoryCommand.extinctionIsMemoryCommandSeparation

------------------------------------------------------------------------
-- Compact interpretation:
--
--   fine state / world
--        |
--        v
--   observer-relative shadow
--        |
--        +--> memory / learned prior / body context
--        |        alter access, valuation and transition gates
--        v
--   current effective action cone
--
-- Corrective refinement need not erase memory.  It may instead change which
-- retained memories command present action, which transitions are accessible,
-- and which future observations become available.
------------------------------------------------------------------------

record PlatoCaveTraumaDecisionBoundary : Set where
  constructor plato-cave-trauma-decision-boundary
  field
    shadowEqualsFineState : Bool
    shadowMeansFalsehood : Bool
    refinementEqualsUltimateReality : Bool
    sameWorldImpliesSameAccessibleCone : Bool
    learnedThreatGateProvesCurrentThreat : Bool
    rememberedContentEqualsCurrentCommand : Bool
    traumaHistoryAloneDeterminesCurrentDecision : Bool
    observerRefinementCanRecoverADeclaredDistinction : Bool

canonicalPlatoCaveTraumaDecisionBoundary :
  PlatoCaveTraumaDecisionBoundary
canonicalPlatoCaveTraumaDecisionBoundary =
  plato-cave-trauma-decision-boundary
    false false false false false false false true
