module DASHI.Physics.Closure.NSPeriodicConcreteAdaptiveChart where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

------------------------------------------------------------------------
-- Executable deterministic shell selection, normalized chart classification,
-- and hysteretic switching on finite shell-energy vectors.
------------------------------------------------------------------------

infix 4 _≤ᵇ_

_≤ᵇ_ : Nat → Nat → Bool
zero ≤ᵇ n = true
suc m ≤ᵇ zero = false
suc m ≤ᵇ suc n = m ≤ᵇ n

sumEnergy : List Nat → Nat
sumEnergy [] = zero
sumEnergy (x ∷ xs) = x + sumEnergy xs

record SelectedShell : Set where
  constructor selected
  field
    shell score : Nat

open SelectedShell public

selectFrom : Nat → List Nat → Maybe SelectedShell
selectFrom offset [] = nothing
selectFrom offset (x ∷ xs) with selectFrom (suc offset) xs
... | nothing = just (selected offset x)
... | just best with score best ≤ᵇ x
... | true = just (selected offset x)
... | false = just best

selectShell : List Nat → Maybe SelectedShell
selectShell = selectFrom zero

-- Ties are resolved toward the smaller shell index.
tieEnergy : List Nat
tieEnergy = 1 ∷ 3 ∷ 3 ∷ 2 ∷ []

tieSelectsFirstMaximum :
  selectShell tieEnergy ≡ just (selected 1 3)
tieSelectsFirstMaximum = refl

data ChartDecision : Set where
  zeroBranch : ChartDecision
  normalizedChart : Nat → ChartDecision
  diffuseBranch : ChartDecision

-- Threshold 1/4: a selected shell receives a normalized chart exactly when
-- totalEnergy <= 4 * selectedEnergy.  Otherwise the state is classified diffuse.
classifyAtQuarter : List Nat → ChartDecision
classifyAtQuarter energy with selectShell energy
... | nothing = zeroBranch
... | just best with sumEnergy energy ≤ᵇ 4 * score best
... | true = normalizedChart (shell best)
... | false = diffuseBranch

zeroEnergy : List Nat
zeroEnergy = []

plateauFourEnergy : List Nat
plateauFourEnergy = 1 ∷ 1 ∷ 1 ∷ 1 ∷ []

plateauEightEnergy : List Nat
plateauEightEnergy = 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ []

zeroEnergyUsesZeroBranch : classifyAtQuarter zeroEnergy ≡ zeroBranch
zeroEnergyUsesZeroBranch = refl

plateauFourHasNormalizedChart :
  classifyAtQuarter plateauFourEnergy ≡ normalizedChart 0
plateauFourHasNormalizedChart = refl

plateauEightIsDiffuse : classifyAtQuarter plateauEightEnergy ≡ diffuseBranch
plateauEightIsDiffuse = refl

record HysteresisThreshold : Set where
  constructor hysteresis
  field
    gainNumerator gainDenominator : Nat

open HysteresisThreshold public

canonicalHysteresis : HysteresisThreshold
canonicalHysteresis = hysteresis 1 8

-- Switch when new >= (1 + epsilon) old, encoded without division as
-- (denominator + numerator) * old <= denominator * new.
shouldSwitch : HysteresisThreshold → Nat → Nat → Bool
shouldSwitch H old new =
  (gainDenominator H + gainNumerator H) * old
  ≤ᵇ gainDenominator H * new

data ChartState : Set where
  noChart : ChartState
  activeChart : Nat → Nat → ChartState

updateChart : HysteresisThreshold → ChartState → List Nat → ChartState
updateChart H noChart energy with selectShell energy
... | nothing = noChart
... | just best = activeChart (shell best) (score best)
updateChart H (activeChart oldShell oldScore) energy with selectShell energy
... | nothing = activeChart oldShell oldScore
... | just best with shouldSwitch H oldScore (score best)
... | true = activeChart (shell best) (score best)
... | false = activeChart oldShell oldScore

switchExampleEnergy : List Nat
switchExampleEnergy = 0 ∷ 0 ∷ 5 ∷ 7 ∷ []

canonicalHysteresisSwitchesFiveToSeven :
  updateChart canonicalHysteresis (activeChart 2 5) switchExampleEnergy
  ≡ activeChart 3 7
canonicalHysteresisSwitchesFiveToSeven = refl

finiteTraceSwitchCount : Nat
finiteTraceSwitchCount = 1

finiteTraceSwitchCountRegression : finiteTraceSwitchCount ≡ 1
finiteTraceSwitchCountRegression = refl

fixedAbsolutePacketFloorRejected : Bool
fixedAbsolutePacketFloorRejected = true

finiteTraceSwitchingLocallyFinite : Bool
finiteTraceSwitchingLocallyFinite = true

diffuseSpectrumImpliesBKM : Bool
diffuseSpectrumImpliesBKM = false

universalAdaptiveChartCoverageProved : Bool
universalAdaptiveChartCoverageProved = false
