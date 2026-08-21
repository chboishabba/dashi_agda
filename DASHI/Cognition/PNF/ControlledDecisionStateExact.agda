module DASHI.Cognition.PNF.ControlledDecisionStateExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Biology.EmbodiedOptionConeInteroceptionExact as Embodied
import DASHI.Cognition.PNF.BoundedEvidenceCommitmentExact as Evidence
import DASHI.Cognition.PNF.DecisionAutonomyExact as Autonomy
import DASHI.Cognition.PNF.DecisionConfidenceNoncollapseExact as Confidence
import DASHI.Cognition.PNF.DecisionConflictAuditSeparationExact as Conflict
import DASHI.Cognition.PNF.DecisionLandscapeFluxExact as Landscape
import DASHI.Cognition.PNF.DecisionStateBundleExact as Bundle
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.NeuromodulatedCommitmentThresholdExact as Threshold
import DASHI.Cognition.PNF.UnifiedDecisionDynamicsExact as Dynamics
import DASHI.Core.IntersectionalNonFactorability as NF

------------------------------------------------------------------------
-- CONTROLLED DECISION STATE
--
-- Stable decision bundle + independently stateful evidence, threshold,
-- confidence, body/interoception, flux and conflict coordinates.
------------------------------------------------------------------------

record ControlledDecisionState : Set where
  constructor controlledDecisionState
  field
    decisionState : Bundle.DecisionStateBundle
    accumulatedEvidence : Evidence.EvidenceLevel
    thresholdPolicy : Threshold.ThresholdPolicy
    confidenceReadout : Confidence.Confidence
    bodyState : Embodied.BodyState
    interoceptiveAfference : Embodied.InteroceptiveAfference
    interoceptivePrior : Embodied.InteroceptivePrior
    feltState : Embodied.FeltState
    fluxRegime : Landscape.FluxRegime
    responseConflict : Conflict.ConflictLevel
    afferenceCoherent :
      interoceptiveAfference ≡ Embodied.afference bodyState
    feltStateCoherent :
      feltState ≡
        Embodied.inferFeltState interoceptivePrior interoceptiveAfference

open ControlledDecisionState public

commitmentReadout : ControlledDecisionState → Evidence.ThresholdCommitment
commitmentReadout state =
  Threshold.thresholdUnder
    (thresholdPolicy state)
    (accumulatedEvidence state)

observedAction : ControlledDecisionState → Dynamics.ExecutedAction
observedAction state = Bundle.observedAction (decisionState state)

canonicalControlled :
  (memory : Memory.MemoryFibre) →
  Confidence.Confidence →
  ControlledDecisionState
canonicalControlled memory confidence =
  controlledDecisionState
    (Bundle.attendedBundle memory)
    Evidence.e1
    Threshold.lowerThreshold
    confidence
    Embodied.regulatedBody
    Embodied.quietAfference
    Embodied.safetyPrior
    Embodied.settledFeeling
    Landscape.noFlux
    Conflict.lowConflict
    refl
    refl

sameThresholdCommitmentCanCarryDifferentConfidence :
  (memory : Memory.MemoryFibre) →
  commitmentReadout (canonicalControlled memory Confidence.lowConfidence)
  ≡ commitmentReadout (canonicalControlled memory Confidence.highConfidence)
  × (confidenceReadout (canonicalControlled memory Confidence.lowConfidence)
      ≡ confidenceReadout (canonicalControlled memory Confidence.highConfidence) → ⊥)
sameThresholdCommitmentCanCarryDifferentConfidence memory = refl , (λ ())

sameEvidenceDifferentThresholdCanChangeCommitment :
  Threshold.thresholdUnder Threshold.lowerThreshold Evidence.e1
  ≡ Threshold.thresholdUnder Threshold.elevatedThreshold Evidence.e1 → ⊥
sameEvidenceDifferentThresholdCanChangeCommitment =
  Threshold.sameEvidenceDifferentThresholdChangesCommitment

record EmbodiedAutonomyState : Set where
  constructor embodiedAutonomyState
  field
    body : Embodied.BodyState
    autonomyAxes : Autonomy.AutonomyAxes

open EmbodiedAutonomyState public

sameBodyAutonomous : EmbodiedAutonomyState
sameBodyAutonomous = embodiedAutonomyState Embodied.mobilisedBody Autonomy.freeAxes

sameBodyConstrained : EmbodiedAutonomyState
sameBodyConstrained = embodiedAutonomyState Embodied.mobilisedBody Autonomy.constrainedAxes

bodyProjection : EmbodiedAutonomyState → Embodied.BodyState
bodyProjection = body

autonomyProjection : EmbodiedAutonomyState → Autonomy.AutonomyAxes
autonomyProjection = autonomyAxes

bodyStateCannotDetermineAutonomyAxes :
  NF.FactorsThrough bodyProjection autonomyProjection → ⊥
bodyStateCannotDetermineAutonomyAxes =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      sameBodyAutonomous
      sameBodyConstrained
      refl
      (λ ()))

mobilisedStateCanCoexistWithAutonomy :
  Autonomy.Autonomous (autonomyAxes sameBodyAutonomous)
mobilisedStateCanCoexistWithAutonomy = Autonomy.freeIsAutonomous

record ControlledDecisionStateBoundary : Set where
  constructor controlledDecisionStateBoundary
  field
    confidenceEqualsCommitment : Bool
    evidenceAloneFixesThreshold : Bool
    bodyStateDeterminesAutonomy : Bool
    feltStateEqualsRawBodyState : Bool
    landscapeEqualsFlux : Bool

canonicalControlledDecisionStateBoundary : ControlledDecisionStateBoundary
canonicalControlledDecisionStateBoundary =
  controlledDecisionStateBoundary false false false false false
