module DASHI.Physics.Closure.NSTriadKNAdaptiveQuarticInvariantRegion where

------------------------------------------------------------------------
-- PROVENANCE
-- Author: Jean-Pierre Aubin.
-- Title: "Viability Theory".
-- Venue/year: Modern Birkhauser Classics, Birkhauser, 2009.
-- DOI: 10.1007/978-0-8176-4910-4.
-- Uses: Chapters 4, 8 and 12 on viability, invariance and Lyapunov functions.
-- Relationship: adapts tangent/inward-pointing invariance architecture to a
-- finite Galerkin flow with adaptive charts and controlled switches.
-- The concentrated/transition/diffuse chart cover is DASHI-original.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_; _<_)

data SpectralRegime : Set where
  zero concentrated transition diffuse : SpectralRegime

record AdaptiveQuarticInvariantRegion {c t s h : Level} :
    Set (lsuc (c ⊔ t ⊔ s ⊔ h)) where
  field
    Cutoff : Set c
    Time : Set t
    State : Set s
    Chart : Set h
    SignedDerivative : Set s

    NonPositive StrictlyNegative : SignedDerivative → Set s

    solution : Cutoff → Time → State
    selectChart : Cutoff → State → Chart
    regime : Cutoff → State → SpectralRegime

    ChartValid : Chart → Cutoff → State → Set
    Admissible : Cutoff → State → Set
    Boundary : Chart → Cutoff → State → Set

    lyapunovValue : Chart → Cutoff → State → Nat
    upperDiniDerivative :
      Chart → Cutoff → State → SignedDerivative

    zeroStateEquilibrium : ∀ N state →
      regime N state ≡ zero →
      Admissible N state

    selectedChartCoversEveryNonzeroRegime : ∀ N state →
      regime N state ≡ concentrated →
      ChartValid (selectChart N state) N state

    selectedChartCoversTransitionRegime : ∀ N state →
      regime N state ≡ transition →
      ChartValid (selectChart N state) N state

    selectedChartCoversDiffuseRegime : ∀ N state →
      regime N state ≡ diffuse →
      ChartValid (selectChart N state) N state

    boundaryPointsInward : ∀ chart N state →
      ChartValid chart N state →
      Boundary chart N state →
      NonPositive (upperDiniDerivative chart N state)

    strictOnDangerousNonzeroBoundary : ∀ chart N state →
      ChartValid chart N state →
      Boundary chart N state →
      regime N state ≡ concentrated →
      StrictlyNegative (upperDiniDerivative chart N state)

    SwitchAllowed : Chart → Chart → Cutoff → State → Set
    switchingDoesNotIncreaseLyapunovValue :
      ∀ old new N state →
      SwitchAllowed old new N state →
      lyapunovValue new N state ≤ lyapunovValue old N state

    dwellSteps : Nat
    positiveDwellTimeBetweenStrictSwitches : 0 < dwellSteps

    InvariantAlong : Cutoff → (Time → State) → Set
    initialTime : Cutoff → Time

    noFirstExitFromLocalInwardnessAndSwitching :
      ∀ N →
      Admissible N (solution N (initialTime N)) →
      InvariantAlong N (solution N)

open AdaptiveQuarticInvariantRegion public

globalAdaptiveInvariance :
  ∀ {c t s h}
    (R : AdaptiveQuarticInvariantRegion {c} {t} {s} {h})
    (N : Cutoff R) →
  Admissible R N (solution R N (initialTime R N)) →
  InvariantAlong R N (solution R N)
globalAdaptiveInvariance R N =
  noFirstExitFromLocalInwardnessAndSwitching R N

adaptiveInvariantRegionArchitectureImplemented : Bool
adaptiveInvariantRegionArchitectureImplemented = true

adaptiveInvariantRegionArchitectureImplementedIsTrue :
  adaptiveInvariantRegionArchitectureImplemented ≡ true
adaptiveInvariantRegionArchitectureImplementedIsTrue = refl

exhaustiveAdaptiveInvarianceClosed : Bool
exhaustiveAdaptiveInvarianceClosed = false

exhaustiveAdaptiveInvarianceClosedIsFalse :
  exhaustiveAdaptiveInvarianceClosed ≡ false
exhaustiveAdaptiveInvarianceClosedIsFalse = refl
