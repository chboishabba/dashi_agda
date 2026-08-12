module DASHI.Core.PathDependentAccessibilityExact where

------------------------------------------------------------------------
-- PATH-DEPENDENT ACCESSIBILITY
--
-- Same public state need not imply the same future cone.  A retained history
-- coordinate may alter which next states are accessible without deleting the
-- currently visible state.  This is the generic finite core behind the
-- provenance-conditioned transition-geometry claim.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- A tiny exact carrier: both states expose `false`, but their histories induce
-- different accessibility kernels under the same probe action.
------------------------------------------------------------------------

data History : Set where
  openingHistory : History
  retainingHistory : History

record AccessibleState : Set where
  constructor accessibleState
  field
    visible : Bool
    history : History

open AccessibleState public

probe : AccessibleState → AccessibleState
probe (accessibleState false openingHistory) =
  accessibleState true openingHistory
probe (accessibleState true openingHistory) =
  accessibleState true openingHistory
probe (accessibleState value retainingHistory) =
  accessibleState value retainingHistory

left right : AccessibleState
left = accessibleState false openingHistory
right = accessibleState false retainingHistory

samePublicNow : visible left ≡ visible right
samePublicNow = refl

futurePublicDiffers : visible (probe left) ≡ visible (probe right) → ⊥
futurePublicDiffers ()

------------------------------------------------------------------------
-- Generic carrier: history selects an accessibility kernel rather than a
-- truth value.  No implication from inaccessible to nonexistent is provided.
------------------------------------------------------------------------

record PathDependentAccessibility
    (State History Action : Set) : Set₁ where
  constructor pathDependentAccessibility
  field
    publicProjection : State → Bool
    provenanceHistory : State → History
    accessibleStep : History → Action → State → State

open PathDependentAccessibility public

record AccessibilityDivergence
    {State History Action : Set}
    (system : PathDependentAccessibility State History Action) : Set₁ where
  constructor accessibilityDivergence
  field
    action : Action
    leftState rightState : State
    samePublicState :
      publicProjection system leftState ≡ publicProjection system rightState
    nextPublicDifferent :
      publicProjection system
        (accessibleStep system
          (provenanceHistory system leftState) action leftState)
      ≡
      publicProjection system
        (accessibleStep system
          (provenanceHistory system rightState) action rightState)
      → ⊥

open AccessibilityDivergence public

data ProbeAction : Set where
  probeAction : ProbeAction

finiteAccessibilitySystem :
  PathDependentAccessibility AccessibleState History ProbeAction
finiteAccessibilitySystem =
  pathDependentAccessibility
    visible
    history
    (λ h action state → stepFor h state)
  where
    stepFor : History → AccessibleState → AccessibleState
    stepFor openingHistory state = probe (accessibleState (visible state) openingHistory)
    stepFor retainingHistory state = probe (accessibleState (visible state) retainingHistory)

finiteHistoryChangesFutureCone : AccessibilityDivergence finiteAccessibilitySystem
finiteHistoryChangesFutureCone =
  accessibilityDivergence
    probeAction
    left
    right
    refl
    (λ equality → futurePublicDiffers equality)

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

data InaccessibilityErasurePermission : Set where

inaccessibilityDoesNotProveNonexistence :
  InaccessibilityErasurePermission → ⊥
inaccessibilityDoesNotProveNonexistence ()
