module DASHI.Cognition.PNF.ControlledFutureSpectralRepresentationExact where

------------------------------------------------------------------------
-- CONTROLLED FUTURE-SUFFICIENT REPRESENTATIONS
--
-- High-level control becomes tractable in a latent carrier only when the
-- action-indexed dynamics really commute with encoding.  If target membership
-- also factors through the latent carrier, then a latent control trajectory
-- reaching a target is an exact certificate that the fine physical trajectory
-- reaches the same declared target.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record ControlledInvariantRepresentation
    (State Control Latent Goal : Set) : Set₁ where
  constructor controlledInvariantRepresentation
  field
    encode : State → Latent
    fineStep : Control → State → State
    latentStep : Control → Latent → Latent

    FineTarget : Goal → State → Set
    LatentTarget : Goal → Latent → Set

    controlIntertwines :
      (control : Control) (state : State) →
      encode (fineStep control state)
      ≡ latentStep control (encode state)

    targetFactorsForward :
      (goal : Goal) (state : State) →
      FineTarget goal state → LatentTarget goal (encode state)

    targetFactorsBackward :
      (goal : Goal) (state : State) →
      LatentTarget goal (encode state) → FineTarget goal state

open ControlledInvariantRepresentation public

runFineControls :
  ∀ {State Control Latent Goal} →
  ControlledInvariantRepresentation State Control Latent Goal →
  List Control → State → State
runFineControls representation [] state = state
runFineControls representation (control ∷ controls) state =
  runFineControls representation controls (fineStep representation control state)

runLatentControls :
  ∀ {State Control Latent Goal} →
  ControlledInvariantRepresentation State Control Latent Goal →
  List Control → Latent → Latent
runLatentControls representation [] latent = latent
runLatentControls representation (control ∷ controls) latent =
  runLatentControls representation controls
    (latentStep representation control latent)

controlledTraceIntertwines :
  ∀ {State Control Latent Goal}
    (representation : ControlledInvariantRepresentation State Control Latent Goal)
    (controls : List Control) (state : State) →
  encode representation (runFineControls representation controls state)
  ≡ runLatentControls representation controls (encode representation state)
controlledTraceIntertwines representation [] state = refl
controlledTraceIntertwines representation (control ∷ controls) state =
  trans
    (controlledTraceIntertwines representation controls
      (fineStep representation control state))
    (cong (runLatentControls representation controls)
      (controlIntertwines representation control state))

latentTargetAfterTraceImpliesFineTarget :
  ∀ {State Control Latent Goal}
    (representation : ControlledInvariantRepresentation State Control Latent Goal)
    (goal : Goal) (controls : List Control) (state : State) →
  LatentTarget representation goal
    (runLatentControls representation controls (encode representation state)) →
  FineTarget representation goal
    (runFineControls representation controls state)
latentTargetAfterTraceImpliesFineTarget representation goal controls state latentTarget =
  targetFactorsBackward representation goal
    (runFineControls representation controls state)
    (subst
      (LatentTarget representation goal)
      (sym (controlledTraceIntertwines representation controls state))
      latentTarget)

fineTargetAfterTraceImpliesLatentTarget :
  ∀ {State Control Latent Goal}
    (representation : ControlledInvariantRepresentation State Control Latent Goal)
    (goal : Goal) (controls : List Control) (state : State) →
  FineTarget representation goal
    (runFineControls representation controls state) →
  LatentTarget representation goal
    (runLatentControls representation controls (encode representation state))
fineTargetAfterTraceImpliesLatentTarget representation goal controls state fineTarget =
  subst
    (LatentTarget representation goal)
    (controlledTraceIntertwines representation controls state)
    (targetFactorsForward representation goal
      (runFineControls representation controls state) fineTarget)

record LatentReachabilityCertificate
    {State Control Latent Goal : Set}
    (representation : ControlledInvariantRepresentation State Control Latent Goal)
    (goal : Goal) (state : State) : Set₁ where
  constructor latentReachabilityCertificate
  field
    controls : List Control
    latentReachesGoal :
      LatentTarget representation goal
        (runLatentControls representation controls (encode representation state))

open LatentReachabilityCertificate public

latentReachabilityCompilesToFineReachability :
  ∀ {State Control Latent Goal}
    {representation : ControlledInvariantRepresentation State Control Latent Goal}
    {goal : Goal} {state : State} →
  LatentReachabilityCertificate representation goal state →
  FineTarget representation goal
    (runFineControls representation
      (controls _) state)
latentReachabilityCompilesToFineReachability certificate =
  latentTargetAfterTraceImpliesFineTarget
    _ _ (controls certificate) _ (latentReachesGoal certificate)

------------------------------------------------------------------------
-- Boundary: this theorem transfers an already-certified latent control plan.
-- It does not assert controllability, minimum-energy control, or that a learned
-- encoder discovers the right target coordinates.  Those remain producer
-- obligations for the morphogenetic basin/control lane.
------------------------------------------------------------------------
