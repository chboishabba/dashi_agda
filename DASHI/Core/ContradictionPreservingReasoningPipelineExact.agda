module DASHI.Core.ContradictionPreservingReasoningPipelineExact where

------------------------------------------------------------------------
-- CONTRADICTION-PRESERVING REASONING PIPELINE
--
-- Source basis:
--   User-supplied DASHI philosophical/anatomy notes reconstruct the mature
--   architecture as a separation between observation, contradiction/tension,
--   structural classification, supervisory authorization, and action.
--
-- Repo reuse:
--   * EpistemicSuspensionExact owns neutral = suspend/refine.
--   * ObserverRefinementLatticeExact owns coarse/fine observer refinement.
--   * ExceptionalSignalLatticeExact owns missing-vs-contradiction severity.
--   * DialecticMotifKernel owns the concrete executable motif -> policy map.
--
-- This module owns only the composition boundary: detecting tension is not
-- itself closure, authorization, or action.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.EpistemicSuspensionExact as Suspension
import DASHI.Core.ExceptionalSignalLatticeExact as Exceptional
import DASHI.Reasoning.DialecticMotifKernel as Motif

------------------------------------------------------------------------
-- Separate pipeline phases.
------------------------------------------------------------------------

data ReasoningPhase : Set where
  observationPhase
  tensionPhase
  classificationPhase
  authorizationPhase
  actionPhase
  : ReasoningPhase

observation≠action : observationPhase ≡ actionPhase → ⊥
observation≠action ()

tension≠authorization : tensionPhase ≡ authorizationPhase → ⊥
tension≠authorization ()

classification≠action : classificationPhase ≡ actionPhase → ⊥
classification≠action ()

------------------------------------------------------------------------
-- Generic typed pipeline.
------------------------------------------------------------------------

record ReasoningPipeline
    (State Observation Tension Classification Authorization Action : Set)
    : Set₁ where
  field
    observe : State → Observation
    detectTension : Observation → Tension
    classify : State → Tension → Classification
    authorize : State → Classification → Authorization
    act : State → Authorization → Action

open ReasoningPipeline public

------------------------------------------------------------------------
-- Concrete policy-level interpretation of the existing motif kernel.
------------------------------------------------------------------------

data Authorization : Set where
  continueAuthorized
  bufferAuthorized
  redesignAuthorized
  timeControlAuthorized
  restrictedAuthorized
  prohibitAuthorized
  liftAuthorized
  : Authorization

authorizationFromPolicy : Motif.Policy → Authorization
authorizationFromPolicy Motif.allow = continueAuthorized
authorizationFromPolicy Motif.timingFence = restrictedAuthorized
authorizationFromPolicy Motif.roleFence = restrictedAuthorized
authorizationFromPolicy Motif.redesign = redesignAuthorized
authorizationFromPolicy Motif.buffer = bufferAuthorized
authorizationFromPolicy Motif.timeControl = timeControlAuthorized
authorizationFromPolicy Motif.programOnly = restrictedAuthorized
authorizationFromPolicy Motif.prohibit = prohibitAuthorized
authorizationFromPolicy Motif.lift = liftAuthorized

m5AuthorizesBuffer :
  authorizationFromPolicy (Motif.policy Motif.M5) ≡ bufferAuthorized
m5AuthorizesBuffer = refl

m9AuthorizesProhibition :
  authorizationFromPolicy (Motif.policy Motif.M9) ≡ prohibitAuthorized
m9AuthorizesProhibition = refl

m10AuthorizesLift :
  authorizationFromPolicy (Motif.policy Motif.M10) ≡ liftAuthorized
m10AuthorizesLift = refl

------------------------------------------------------------------------
-- Uncertainty and contradiction have different control meanings.
------------------------------------------------------------------------

neutralEvidenceStillSuspends :
  Suspension.disposition Suspension.neutralEvidence
  ≡ Suspension.suspendAndRefine
neutralEvidenceStillSuspends = refl

contradictionSurvivesMissingAggregation :
  Exceptional._⊔E_ Exceptional.qPARA Exceptional.qVOID
  ≡ Exceptional.qPARA
contradictionSurvivesMissingAggregation =
  Exceptional.paradoxDominatesVoid

------------------------------------------------------------------------
-- No direct M5 -> M9 theorem is manufactured here.  The types make the reason
-- explicit: epistemic disposition and motif authorization are different
-- layers, and promotion requires an application-supplied classifier/guard.
------------------------------------------------------------------------

data SuspensionToProhibitionPromotion : Set where

noAutomaticSuspensionToProhibition :
  SuspensionToProhibitionPromotion → ⊥
noAutomaticSuspensionToProhibition ()

record ContradictionPreservingPipelineBoundary : Set where
  constructor contradiction-preserving-pipeline-boundary
  field
    observationDirectlyIsAction : Bool
    observationDirectlyIsActionIsFalse : observationDirectlyIsAction ≡ false
    tensionAutomaticallyIsCatastrophe : Bool
    tensionAutomaticallyIsCatastropheIsFalse :
      tensionAutomaticallyIsCatastrophe ≡ false
    uncertaintyAutomaticallyAuthorizesProhibition : Bool
    uncertaintyAutomaticallyAuthorizesProhibitionIsFalse :
      uncertaintyAutomaticallyAuthorizesProhibition ≡ false
    contradictionMayBeRetainedAsInformation : Bool
    contradictionMayBeRetainedAsInformationIsTrue :
      contradictionMayBeRetainedAsInformation ≡ true
    authorizationIsTruth : Bool
    authorizationIsTruthIsFalse : authorizationIsTruth ≡ false

canonicalContradictionPreservingPipelineBoundary :
  ContradictionPreservingPipelineBoundary
canonicalContradictionPreservingPipelineBoundary =
  contradiction-preserving-pipeline-boundary
    false refl false refl false refl true refl false refl
