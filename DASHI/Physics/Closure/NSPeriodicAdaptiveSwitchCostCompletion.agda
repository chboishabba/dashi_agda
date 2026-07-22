module DASHI.Physics.Closure.NSPeriodicAdaptiveSwitchCostCompletion where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; false)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Universal hysteretic switching surface.
--
-- The executable finite selector already exists.  This module names the exact
-- trajectory-level facts needed to use it in an analytic proof: score gain at a
-- switch, exclusion of immediate chattering, local finiteness or summable switch
-- costs, and control of potential jumps by the selected switch budget.
------------------------------------------------------------------------

data SwitchingControl
    {l f : Level}
    (LocallyFinite : Set l)
    (Summable : Set f) : Set (l ⊔ f) where
  locallyFiniteControl : LocallyFinite → SwitchingControl LocallyFinite Summable
  summableControl : Summable → SwitchingControl LocallyFinite Summable

record PeriodicAdaptiveSwitchCostInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (Time State Shell : Set i) : Set (lsuc i) where
  field
    ActiveShell : Time → State → Shell
    SwitchEvent : Time → State → Set i

    shellScore : Shell → Time → State → Scalar A
    potentialBefore potentialAfter switchCost :
      Time → State → Scalar A

    totalSwitchCost : Scalar A

    HysteresisGainAtSwitch : Time → State → Set i
    NoImmediateBackSwitch : Time → State → Set i
    LocallyFiniteSwitching : Set i
    SummableSwitchCosts : Set i

    hysteresisGainAtSwitch : ∀ τ u →
      SwitchEvent τ u → HysteresisGainAtSwitch τ u

    noImmediateBackSwitch : ∀ τ u →
      SwitchEvent τ u → NoImmediateBackSwitch τ u

    switchPotentialJumpBound : ∀ τ u →
      SwitchEvent τ u →
      _≤_ A (potentialAfter τ u) (_+_ A (potentialBefore τ u) (switchCost τ u))

    eachSwitchCostBelowTotal : ∀ τ u →
      SwitchEvent τ u →
      _≤_ A (switchCost τ u) totalSwitchCost

    switchingControl :
      SwitchingControl LocallyFiniteSwitching SummableSwitchCosts

    summedPotentialJump : Scalar A

    sumSwitchJumpsBelowTotal :
      _≤_ A summedPotentialJump totalSwitchCost

open PeriodicAdaptiveSwitchCostInputs public

adaptiveSwitchingIsControlled :
  ∀ {i} {A : AbsorptionArithmetic}
    {Time State Shell : Set i} →
  (S : PeriodicAdaptiveSwitchCostInputs A Time State Shell) →
  LocallyFiniteSwitching S ⊎ SummableSwitchCosts S
adaptiveSwitchingIsControlled S with switchingControl S
... | locallyFiniteControl finite = inj₁ finite
... | summableControl summable = inj₂ summable

singleSwitchPotentialBelowGlobalBudget :
  ∀ {i} {A : AbsorptionArithmetic}
    {Time State Shell : Set i} →
  (S : PeriodicAdaptiveSwitchCostInputs A Time State Shell) →
  ∀ τ u →
  SwitchEvent S τ u →
  _≤_ A
    (potentialAfter S τ u)
    (_+_ A (potentialBefore S τ u) (totalSwitchCost S))
singleSwitchPotentialBelowGlobalBudget {A = A} S τ u switch =
  ≤-trans A
    (switchPotentialJumpBound S τ u switch)
    (additionMonotoneLeft A (eachSwitchCostBelowTotal S τ u switch))

adaptiveTotalSwitchCostBound :
  ∀ {i} {A : AbsorptionArithmetic}
    {Time State Shell : Set i} →
  (S : PeriodicAdaptiveSwitchCostInputs A Time State Shell) →
  _≤_ A (summedPotentialJump S) (totalSwitchCost S)
adaptiveTotalSwitchCostBound = sumSwitchJumpsBelowTotal

------------------------------------------------------------------------
-- Proof-level and fail-closed status.
------------------------------------------------------------------------

adaptiveSwitchCostAssemblyLevel : ProofLevel
adaptiveSwitchCostAssemblyLevel = machineChecked

universalHysteresisNoChatteringLevel : ProofLevel
universalHysteresisNoChatteringLevel = conditional

universalSwitchCostSummabilityLevel : ProofLevel
universalSwitchCostSummabilityLevel = conjectural

adaptiveSwitchCostInputsInhabited : Bool
adaptiveSwitchCostInputsInhabited = false
