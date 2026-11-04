{-# OPTIONS --safe #-}
module DASHI.Education.DigitalESDWorldPNFTrialecticControlBridgeExact where

------------------------------------------------------------------------
-- Same-object ESD study/world -> PNF -> dialectic/trialectic -> actions.
--
-- Reuses existing source-paid ESD AccountedStudyWorld, canonical PNF
-- world-model and action-conditioned world-model owners.  No empirical
-- observation, source review, semantic reading or authority is invented.
--
-- Dialectic: an interpreted two-sided PNF relation is a candidate until
-- independently admitted.  Trialectic: its third face is not determined
-- by three pairwise edge dispositions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.List.Base as List using ()
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDOpenAxisStudyPartWorldExact as World
import DASHI.Education.DigitalESDOpenAxisGapTransportExact as Gap
import DASHI.WorldModel.PredicateNormalWorldModelCore as PNW
import DASHI.WorldModel.ActionConditionedWorldModelCore as Action
import DASHI.Core.ContactGateCore as Gate
import DASHI.Reasoning.TrialecticBoundaryFaceNonfactorabilityExact as Tri
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

------------------------------------------------------------------------
-- WPC00: A single AccountedStudyWorld is preserved while the same source
-- address is normalised.  A caller supplies actual observation and an
-- equality identifying its PNF; no title/metadata shortcut is available.
------------------------------------------------------------------------

record SameObjectStudyPNF
    (scope : World.StudyWorldScope)
    (model : PNW.PredicateNormalWorldModelCore) : Set₂ where
  constructor same-object-study-pnf
  field
    world : World.AccountedStudyWorld scope
    observationAt :
      (s : World.Study scope) →
      (p : World.Part scope s) →
      (axis : World.Axis scope) →
      PNW.Observation model
    pnfAt :
      (s : World.Study scope) →
      (p : World.Part scope s) →
      (axis : World.Axis scope) →
      PNW.PNF model
    actualNormalisation :
      (s : World.Study scope) →
      (p : World.Part scope s) →
      (axis : World.Axis scope) →
      PNW.normalize model
        (PNW.encodeCarrier model (observationAt s p axis)) ≡
      pnfAt s p axis
    candidateOnly :
      (s : World.Study scope) →
      (p : World.Part scope s) →
      (axis : World.Axis scope) →
      PNW.PredicateNormalProposalBoundary model (observationAt s p axis)

open SameObjectStudyPNF public

-- WPC01: The canonical candidate action generator is the one used for
-- the SAME original observation, not a source-description surrogate.
candidateActionsAt :
  {scope : World.StudyWorldScope} →
  {model : PNW.PredicateNormalWorldModelCore} →
  (bridge : SameObjectStudyPNF scope model) →
  (s : World.Study scope) →
  (p : World.Part scope s) →
  (axis : World.Axis scope) →
  List (PNW.Action model)
candidateActionsAt {model = model} bridge s p axis =
  PNW.candidateActions model (observationAt bridge s p axis)

-- WPC02: PNF/probe candidate generation cannot silently promote truth.
phiRemainsProposalOnly :
  {scope : World.StudyWorldScope} →
  {model : PNW.PredicateNormalWorldModelCore} →
  (bridge : SameObjectStudyPNF scope model) →
  (s : World.Study scope) →
  (p : World.Part scope s) →
  (axis : World.Axis scope) →
  PNW.phiPromotesTruth model ≡ false
phiRemainsProposalOnly bridge s p axis =
  PNW.phiIsProposalOnly (candidateOnly bridge s p axis)

psiRemainsProposalOnly :
  {scope : World.StudyWorldScope} →
  {model : PNW.PredicateNormalWorldModelCore} →
  (bridge : SameObjectStudyPNF scope model) →
  (s : World.Study scope) →
  (p : World.Part scope s) →
  (axis : World.Axis scope) →
  PNW.psiPromotesTruth model ≡ false
psiRemainsProposalOnly bridge s p axis =
  PNW.psiIsProposalOnly (candidateOnly bridge s p axis)

-- WPC03: An independently typed three-position relation retains its
-- original PNF readings AND its irreducible face.  The proposed face is
-- deliberately not construed as reviewed evidence from those studies.
record SourceIndexedTrialectic
    {scope : World.StudyWorldScope}
    {model : PNW.PredicateNormalWorldModelCore}
    (bridge : SameObjectStudyPNF scope model) : Set₂ where
  constructor source-indexed-trialectic
  field
    positionA positionB positionC : World.StudyPart scope
    axis : World.Axis scope

    pnfA : PNW.PNF model
    pnfB : PNW.PNF model
    pnfC : PNW.PNF model

    sourceReadingA :
      pnfA ≡ pnfAt bridge
        (World.study positionA) (World.part positionA) axis
    sourceReadingB :
      pnfB ≡ pnfAt bridge
        (World.study positionB) (World.part positionB) axis
    sourceReadingC :
      pnfC ≡ pnfAt bridge
        (World.study positionC) (World.part positionC) axis

    relation : Tri.TrialecticState
    dyadicView : Tri.TrialecticBoundary
    sourceIndexedBoundary :
      Tri.boundaryObserver relation ≡ dyadicView

open SourceIndexedTrialectic public

-- WPC04: Reuse the ACTUAL trialectic non-descent theorem.
-- Three mutually specified edge dispositions cannot determine the face.
threeDyadsCannotDetermineFace :
  Descent.FactorsThrough
    Tri.boundaryObserver Tri.faceConsumer → ⊥
threeDyadsCannotDetermineFace =
  Tri.triadicFaceCannotFactorThroughThreeEdges

-- WPC05: A cross-study gap on this identical world is a question, not a
-- new recipient observation.  The existing gap owner enforces distinct
-- canonical source URLs and a recipient review-status witness.
record SameWorldGapPNF
    {scope : World.StudyWorldScope}
    {model : PNW.PredicateNormalWorldModelCore}
    (bridge : SameObjectStudyPNF scope model) : Set₂ where
  constructor same-world-gap-pnf
  field
    donor recipient : World.StudyPart scope
    axis : World.Axis scope
    sourcePaidGap :
      Gap.CandidateGapQuestionRoute
        scope (world bridge) donor recipient axis
    donorReading :
      PNW.PNF model
    recipientReading :
      PNW.PNF model
    donorReadingCorrect :
      donorReading ≡
      pnfAt bridge (World.study donor) (World.part donor) axis
    recipientReadingCorrect :
      recipientReading ≡
      pnfAt bridge (World.study recipient) (World.part recipient) axis

open SameWorldGapPNF public

gapStillNeedsSourceReview :
  {scope : World.StudyWorldScope} →
  {model : PNW.PredicateNormalWorldModelCore} →
  {bridge : SameObjectStudyPNF scope model} →
  (candidate : SameWorldGapPNF bridge) →
  Gap.RecipientGapStatus scope (world bridge)
    (recipient candidate) (axis candidate)
gapStillNeedsSourceReview candidate =
  Gap.targetStatus (sourcePaidGap candidate)

-- WPC06: Prospective action handoff is separately guarded.  A selected
-- action sequence needs the actual action-model promotion witness.
record GovernedStudyActionHandoff
    {scope : World.StudyWorldScope}
    {pnf : PNW.PredicateNormalWorldModelCore}
    (source : SameObjectStudyPNF scope pnf)
    (model : Action.ActionConditionedWorldModelCore) : Set₂ where
  constructor governed-study-action-handoff
  field
    focus : World.StudyPart scope
    axis : World.Axis scope
    stateOfObservation : PNW.Carrier pnf → Action.State model
    translateAction : PNW.Action pnf → Action.Action model
    dependency : Action.Dependency model
    selected : Action.SelectedActionSequence model dependency

    selectedMatchesActualPNF :
      Action.actions selected ≡
      List.map translateAction
        (candidateActionsAt source
          (World.study focus) (World.part focus) axis)

open GovernedStudyActionHandoff public

-- WPC07: The selected handoff is authorisation-carrying, not merely
-- a high spectral score or a proposed intervention.
selectedHandoffHasAuthority :
  {scope : World.StudyWorldScope} →
  {pnf : PNW.PredicateNormalWorldModelCore} →
  {source : SameObjectStudyPNF scope pnf} →
  {model : Action.ActionConditionedWorldModelCore} →
  (handoff : GovernedStudyActionHandoff source model) →
  Gate.authorityGateClosed
    (Action.actionGate model
      (Action.actions (selected handoff))) ≡ true
selectedHandoffHasAuthority {model = model} handoff =
  Action.selectedActionAuthorityClosed
    model (dependency handoff) (selected handoff)

-- The predicted trajectory is not a measured educational outcome.
predictedStudyTrajectory :
  {scope : World.StudyWorldScope} →
  {pnf : PNW.PredicateNormalWorldModelCore} →
  {source : SameObjectStudyPNF scope pnf} →
  {model : Action.ActionConditionedWorldModelCore} →
  (handoff : GovernedStudyActionHandoff source model) →
  Action.Trajectory model
predictedStudyTrajectory {pnf = pnf} {source = source}
                         {model = model} handoff =
  Action.predictedTrajectory model
    (stateOfObservation handoff
      (PNW.encodeCarrier pnf
        (observationAt source
          (World.study (focus handoff))
          (World.part (focus handoff))
          (axis handoff))))
    (selected handoff)
