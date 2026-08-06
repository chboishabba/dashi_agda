module DASHI.Physics.Closure.NSTriadKNLuoFiniteMeanValueGronwallExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Mathematical ingredient: finite mean-value selection followed by discrete
-- Gronwall propagation.  No DOI is assigned to this repository-specialised
-- induction theorem.
--
-- PURPOSE
-- Compose the checked finite mean-value selector with the checked discrete
-- Gronwall theorem without introducing division.  If the selected minimum of
-- a nonempty time window is used as the initial energy, its window-cardinality
-- multiple is bounded by the window sum.  Scaling the full recurrence by that
-- same cardinality gives an exact Gronwall estimate with the window sum as the
-- initial bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteMeanValueSelectionExact as Mean
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDiscreteGronwallExact as Gronwall

natScaleMonotone :
  (count : Nat) →
  ∀ {left right : ℚ} →
  left ≤ right →
  Mean.natScale count left ≤ Mean.natScale count right
natScaleMonotone zero inequality = ℚₚ.≤-refl
natScaleMonotone (suc count) inequality =
  ℚₚ.+-mono-≤
    inequality
    (natScaleMonotone count inequality)

natScaleAdd :
  (count : Nat) →
  (left right : ℚ) →
  Mean.natScale count (left + right)
  ≡ Mean.natScale count left + Mean.natScale count right
natScaleAdd zero left right = solve []
natScaleAdd (suc count) left right
  rewrite natScaleAdd count left right =
  solve
    ( left
    ∷ right
    ∷ Mean.natScale count left
    ∷ Mean.natScale count right
    ∷ []
    )

natScaleMultiply :
  (count : Nat) →
  (scale value : ℚ) →
  Mean.natScale count (scale * value)
  ≡ scale * Mean.natScale count value
natScaleMultiply zero scale value = solve []
natScaleMultiply (suc count) scale value
  rewrite natScaleMultiply count scale value =
  solve
    ( scale
    ∷ value
    ∷ Mean.natScale count value
    ∷ []
    )

record FiniteMeanValueGronwallData : Set₁ where
  field
    windowHead : ℚ
    windowTail : List ℚ

    energy forcing : Nat → ℚ
    growth : ℚ

    growthNonnegative : 0ℚ ≤ growth

    initialEnergyIsSelectedMinimum :
      energy zero
      ≡ Mean.selected
          (Mean.finiteMeanValueSelection windowHead windowTail)

    oneStepBound :
      (step : Nat) →
      energy (suc step)
      ≤ growth * energy step + forcing step

open FiniteMeanValueGronwallData public

windowValues : FiniteMeanValueGronwallData → List ℚ
windowValues data = windowHead data ∷ windowTail data

windowCount : FiniteMeanValueGronwallData → Nat
windowCount data = Mean.listLength (windowValues data)

scaledEnergy : FiniteMeanValueGronwallData → Nat → ℚ
scaledEnergy data step =
  Mean.natScale (windowCount data) (energy data step)

scaledForcing : FiniteMeanValueGronwallData → Nat → ℚ
scaledForcing data step =
  Mean.natScale (windowCount data) (forcing data step)

scaledOneStepBound :
  (data : FiniteMeanValueGronwallData) →
  (step : Nat) →
  scaledEnergy data (suc step)
  ≤ growth data * scaledEnergy data step + scaledForcing data step
scaledOneStepBound data step =
  let
    count = windowCount data

    scaledRaw :
      Mean.natScale count (energy data (suc step))
      ≤ Mean.natScale count
          (growth data * energy data step + forcing data step)
    scaledRaw =
      natScaleMonotone count (oneStepBound data step)

    targetMeaning :
      Mean.natScale count
        (growth data * energy data step + forcing data step)
      ≡ growth data * Mean.natScale count (energy data step)
        + Mean.natScale count (forcing data step)
    targetMeaning =
      let
        addition =
          natScaleAdd count
            (growth data * energy data step)
            (forcing data step)
        multiplication =
          natScaleMultiply count (growth data) (energy data step)
      in
      subst
        (λ leftScaled →
          Mean.natScale count
            (growth data * energy data step + forcing data step)
          ≡ leftScaled + Mean.natScale count (forcing data step))
        multiplication
        addition
  in
  subst
    (λ upper → scaledEnergy data (suc step) ≤ upper)
    targetMeaning
    scaledRaw

scaledInitialEnergyBelowWindowSum :
  (data : FiniteMeanValueGronwallData) →
  scaledEnergy data zero ≤ Mean.sumValues (windowValues data)
scaledInitialEnergyBelowWindowSum data =
  let
    selection =
      Mean.finiteMeanValueSelection
        (windowHead data)
        (windowTail data)
  in
  subst
    (λ initial →
      Mean.natScale (windowCount data) initial
      ≤ Mean.sumValues (windowValues data))
    (sym (initialEnergyIsSelectedMinimum data))
    (Mean.crossMultipliedAverageBound selection)

scaledMeanValueGronwallData :
  FiniteMeanValueGronwallData →
  Gronwall.FiniteDiscreteGronwallData
scaledMeanValueGronwallData data = record
  { energy = scaledEnergy data
  ; forcing = scaledForcing data
  ; growth = growth data
  ; initialBound = Mean.sumValues (windowValues data)
  ; growthNonnegative = growthNonnegative data
  ; initialEnergyBound = scaledInitialEnergyBelowWindowSum data
  ; oneStepBound = scaledOneStepBound data
  }

finiteMeanValueGronwall :
  (data : FiniteMeanValueGronwallData) →
  (step : Nat) →
  scaledEnergy data step
  ≤ Gronwall.gronwallEnvelope
      (growth data)
      (scaledForcing data)
      (Mean.sumValues (windowValues data))
      step
finiteMeanValueGronwall data =
  Gronwall.finiteDiscreteGronwall
    (scaledMeanValueGronwallData data)

finiteMeanValueGronwallClosed : Bool
finiteMeanValueGronwallClosed = true

finiteMeanValueInitialAverageTransportClosed : Bool
finiteMeanValueInitialAverageTransportClosed = true

finiteMeanValueGronwallClosedIsTrue :
  finiteMeanValueGronwallClosed ≡ true
finiteMeanValueGronwallClosedIsTrue = refl

finiteMeanValueInitialAverageTransportClosedIsTrue :
  finiteMeanValueInitialAverageTransportClosed ≡ true
finiteMeanValueInitialAverageTransportClosedIsTrue = refl
