module DASHI.Promotion.MetacognitiveFrameBearingState where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Foundations.Base12369RoleHierarchy as Roles
import DASHI.Promotion.SystemicDistressReframingBoundary as Distress

------------------------------------------------------------------------
-- The 1.0 -> 1.1 move is a second-order change of position, not a literal
-- ten-percent increase in facts or a guaranteed therapeutic effect.

 data ReflexiveStance : Set where
  immersedInFrame : ReflexiveStance
  observingFrame : ReflexiveStance

stancePolarity : ReflexiveStance → Roles.BinaryPolarity
stancePolarity immersedInFrame = Roles.polarity-0
stancePolarity observingFrame = Roles.polarity-1

record FrameBearingState
  (Experience Frame Provenance Residual : Set) : Set where
  constructor frameBearingState
  field
    experience : Experience
    frame : Frame
    provenance : Provenance
    residual : Residual
    stance : ReflexiveStance

open FrameBearingState public

pairWithFrame :
  ∀ {Experience Frame : Set} →
  Experience → Frame → Experience × Frame
pairWithFrame x f = x , f

pairPreservesExperience :
  ∀ {Experience Frame : Set} →
  (x : Experience) →
  (f : Frame) →
  proj₁ (pairWithFrame x f) ≡ x
pairPreservesExperience x f = refl

pairExposesFrame :
  ∀ {Experience Frame : Set} →
  (x : Experience) →
  (f : Frame) →
  proj₂ (pairWithFrame x f) ≡ f
pairExposesFrame x f = refl

------------------------------------------------------------------------
-- One exact finite witness.

data Experience1 : Set where
  livedDistress : Experience1

data Frame1 : Set where
  selfFailureFrame systemicOrganisationFrame : Frame1

data Provenance1 : Set where
  firstPersonProvenance : Provenance1

data Residual1 : Set where
  unexplainedRemainder : Residual1

canonicalFrameBearingState :
  FrameBearingState Experience1 Frame1 Provenance1 Residual1
canonicalFrameBearingState =
  frameBearingState
    livedDistress
    systemicOrganisationFrame
    firstPersonProvenance
    unexplainedRemainder
    observingFrame

canonicalExperiencePreserved :
  experience canonicalFrameBearingState ≡ livedDistress
canonicalExperiencePreserved = refl

canonicalFrameExposed :
  frame canonicalFrameBearingState ≡ systemicOrganisationFrame
canonicalFrameExposed = refl

canonicalStanceUsesBinaryAxis :
  stancePolarity (stance canonicalFrameBearingState) ≡ Roles.polarity-1
canonicalStanceUsesBinaryAxis = refl

------------------------------------------------------------------------
-- Four layers which must not be silently collapsed.

data ExplanatoryLayer : Set where
  experienceLayer : ExplanatoryLayer
  interpretationLayer : ExplanatoryLayer
  socialExplanationLayer : ExplanatoryLayer
  actionMandateLayer : ExplanatoryLayer

record MetacognitivePowerUpBoundary : Set where
  constructor metacognitivePowerUpBoundary
  field
    existingDistressSignal : Distress.DistressSignal
    experienceIsPreserved : Bool
    frameIsMadeExplicit : Bool
    residualIsRetained : Bool
    literalTenPercentKnowledgeGainClaimed : Bool
    literalTenPercentKnowledgeGainClaimedIsFalse :
      literalTenPercentKnowledgeGainClaimed ≡ false
    frameAwarenessProvesCause : Bool
    frameAwarenessProvesCauseIsFalse : frameAwarenessProvesCause ≡ false
    frameAwarenessMandatesAction : Bool
    frameAwarenessMandatesActionIsFalse :
      frameAwarenessMandatesAction ≡ false
    symptomReliefGuaranteed : Bool
    symptomReliefGuaranteedIsFalse : symptomReliefGuaranteed ≡ false
    interpretation : String

canonicalMetacognitivePowerUpBoundary : MetacognitivePowerUpBoundary
canonicalMetacognitivePowerUpBoundary =
  metacognitivePowerUpBoundary
    Distress.canonicalDistressSignal
    true
    true
    true
    false refl
    false refl
    false refl
    false refl
    "1.1 knowledge is represented as an experience-preserving frame-bearing state x -> (x, frame, provenance, residual); causal and action authority remain separately evidence-gated"
