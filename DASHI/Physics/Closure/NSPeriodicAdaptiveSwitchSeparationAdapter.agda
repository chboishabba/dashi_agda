module DASHI.Physics.Closure.NSPeriodicAdaptiveSwitchSeparationAdapter where

open import Agda.Primitive using (Level; lsuc)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicHysteresisSeparation as Separation
import DASHI.Physics.Closure.NSPeriodicAdaptiveSwitchCostCompletion as Switch
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Constructor deriving the no-immediate-back-switch field from the exact
-- double-gap/double-modulus separation theorem.
------------------------------------------------------------------------

record PeriodicAdaptiveSwitchSeparationInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (Time State Shell : Set i) : Set (lsuc i) where
  field
    ActiveShell : Time → State → Shell
    SwitchEvent ImmediateBackSwitch : Time → State → Set i

    shellScore : Shell → Time → State → Scalar A
    potentialBefore potentialAfter switchCost :
      Time → State → Scalar A
    totalSwitchCost : Scalar A

    HysteresisGainAtSwitch : Time → State → Set i
    LocallyFiniteSwitching SummableSwitchCosts : Set i

    hysteresisGainAtSwitch : ∀ τ u →
      SwitchEvent τ u → HysteresisGainAtSwitch τ u

    separationForImmediateBackSwitch : ∀ τ u →
      SwitchEvent τ u →
      ImmediateBackSwitch τ u →
      Separation.PeriodicHysteresisSeparationInputs A

    gapDominatesShortIntervalModulus : ∀ τ u
      (switch : SwitchEvent τ u)
      (back : ImmediateBackSwitch τ u) →
      let H = separationForImmediateBackSwitch τ u switch back in
      (_≤_ A
        (_+_ A
          (Separation.hysteresisGap H)
          (Separation.hysteresisGap H))
        (_+_ A
          (Separation.scoreModulus H)
          (Separation.scoreModulus H)) → ⊥)

    switchPotentialJumpBound : ∀ τ u →
      SwitchEvent τ u →
      _≤_ A (potentialAfter τ u)
        (_+_ A (potentialBefore τ u) (switchCost τ u))

    eachSwitchCostBelowTotal : ∀ τ u →
      SwitchEvent τ u →
      _≤_ A (switchCost τ u) totalSwitchCost

    switchingControl :
      Switch.SwitchingControl LocallyFiniteSwitching SummableSwitchCosts

    summedPotentialJump : Scalar A

    sumSwitchJumpsBelowTotal :
      _≤_ A summedPotentialJump totalSwitchCost

open PeriodicAdaptiveSwitchSeparationInputs public

separationExcludesImmediateBackSwitch :
  ∀ {i} {A : AbsorptionArithmetic}
    {Time State Shell : Set i} →
  (S : PeriodicAdaptiveSwitchSeparationInputs A Time State Shell) →
  ∀ τ u →
  SwitchEvent S τ u →
  ImmediateBackSwitch S τ u →
  ⊥
separationExcludesImmediateBackSwitch S τ u switch back =
  Separation.hysteresisGapExcludesImmediateBackSwitch H
    (gapDominatesShortIntervalModulus S τ u switch back)
  where
  H = separationForImmediateBackSwitch S τ u switch back

switchSeparationToAdaptiveSwitchInputs :
  ∀ {i} {A : AbsorptionArithmetic}
    {Time State Shell : Set i} →
  PeriodicAdaptiveSwitchSeparationInputs A Time State Shell →
  Switch.PeriodicAdaptiveSwitchCostInputs A Time State Shell
switchSeparationToAdaptiveSwitchInputs S = record
  { ActiveShell = ActiveShell S
  ; SwitchEvent = SwitchEvent S
  ; shellScore = shellScore S
  ; potentialBefore = potentialBefore S
  ; potentialAfter = potentialAfter S
  ; switchCost = switchCost S
  ; totalSwitchCost = totalSwitchCost S
  ; HysteresisGainAtSwitch = HysteresisGainAtSwitch S
  ; NoImmediateBackSwitch = λ τ u → ImmediateBackSwitch S τ u → ⊥
  ; LocallyFiniteSwitching = LocallyFiniteSwitching S
  ; SummableSwitchCosts = SummableSwitchCosts S
  ; hysteresisGainAtSwitch = hysteresisGainAtSwitch S
  ; noImmediateBackSwitch = separationExcludesImmediateBackSwitch S
  ; switchPotentialJumpBound = switchPotentialJumpBound S
  ; eachSwitchCostBelowTotal = eachSwitchCostBelowTotal S
  ; switchingControl = switchingControl S
  ; summedPotentialJump = summedPotentialJump S
  ; sumSwitchJumpsBelowTotal = sumSwitchJumpsBelowTotal S
  }

adaptiveSwitchControlFromSeparation :
  ∀ {i} {A : AbsorptionArithmetic}
    {Time State Shell : Set i} →
  (S : PeriodicAdaptiveSwitchSeparationInputs A Time State Shell) →
  LocallyFiniteSwitching S ⊎ SummableSwitchCosts S
adaptiveSwitchControlFromSeparation S =
  Switch.adaptiveSwitchingIsControlled
    (switchSeparationToAdaptiveSwitchInputs S)

------------------------------------------------------------------------
-- Status: immediate back-switch exclusion is no longer an opaque field.  The
-- remaining trajectory theorem is the uniform score-modulus estimate and the
-- locally-finite or summable-cost branch.
------------------------------------------------------------------------

adaptiveSwitchSeparationAdapterLevel : ProofLevel
adaptiveSwitchSeparationAdapterLevel = machineChecked
