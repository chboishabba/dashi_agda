module DASHI.Physics.Closure.NSTriadKNLuoFiniteWeightedMeanValueGronwallExact where

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
-- Mathematical ingredients: weighted finite mean-value selection and
-- nonuniform discrete Gronwall propagation.
-- DOI: not assigned to this repository-specialised composition.
--
-- PURPOSE
-- Compose the two finite theorems in the same division-free form needed by a
-- nonuniform time partition.  If the recurrence begins at the selected
-- minimum of a weighted window, scale the complete recurrence by the total
-- window mass.  The initial scaled energy is then bounded by the weighted
-- first moment, and nonuniform Gronwall propagates that bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteWeightedJensenExact as Weighted
import DASHI.Physics.Closure.NSTriadKNLuoFiniteWeightedMeanValueSelectionExact as Mean
import DASHI.Physics.Closure.NSTriadKNLuoFiniteNonuniformGronwallExact as Gronwall

massNonnegative :
  (samples : List Weighted.WeightedValue) →
  0ℚ ≤ Weighted.mass samples
massNonnegative [] = ℚₚ.≤-refl
massNonnegative (sample ∷ samples) =
  L2.addNonnegative
    (Weighted.weightNonnegative sample)
    (massNonnegative samples)

scaleStep : ℚ → Gronwall.GronwallStep → Gronwall.GronwallStep
scaleStep scale stepValue =
  Gronwall.gronwall-step
    (Gronwall.growth stepValue)
    (scale * Gronwall.forcing stepValue)
    (Gronwall.growthNonnegative stepValue)

scaleSteps : ℚ → List Gronwall.GronwallStep → List Gronwall.GronwallStep
scaleSteps scale [] = []
scaleSteps scale (stepValue ∷ steps) =
  scaleStep scale stepValue ∷ scaleSteps scale steps

scaleOneStepBound :
  (scale : ℚ) →
  0ℚ ≤ scale →
  (stepValue : Gronwall.GronwallStep) →
  ∀ {current next} →
  next ≤ (1ℚ + Gronwall.growth stepValue) * current
    + Gronwall.forcing stepValue →
  scale * next
  ≤ (1ℚ + Gronwall.growth stepValue) * (scale * current)
    + scale * Gronwall.forcing stepValue
scaleOneStepBound
  scale scaleNonnegative stepValue {current} {next} originalBound =
  let
    scaledRaw :
      scale * next
      ≤ scale
        * ((1ℚ + Gronwall.growth stepValue) * current
          + Gronwall.forcing stepValue)
    scaledRaw =
      let instance scaleIsNonnegative = nonNegative scaleNonnegative
      in ℚₚ.*-monoˡ-≤-nonNeg scale originalBound

    targetMeaning :
      scale
        * ((1ℚ + Gronwall.growth stepValue) * current
          + Gronwall.forcing stepValue)
      ≡ (1ℚ + Gronwall.growth stepValue) * (scale * current)
        + scale * Gronwall.forcing stepValue
    targetMeaning =
      solve
        ( scale
        ∷ Gronwall.growth stepValue
        ∷ current
        ∷ Gronwall.forcing stepValue
        ∷ []
        )
  in
  subst
    (λ upper → scale * next ≤ upper)
    targetMeaning
    scaledRaw

scalePath :
  (scale : ℚ) →
  0ℚ ≤ scale →
  ∀ {initial terminal steps} →
  Gronwall.GronwallPath initial steps terminal →
  Gronwall.GronwallPath
    (scale * initial)
    (scaleSteps scale steps)
    (scale * terminal)
scalePath scale scaleNonnegative (Gronwall.finished energy) =
  Gronwall.finished (scale * energy)
scalePath scale scaleNonnegative
  (Gronwall.advance stepValue nextBound restPath) =
  Gronwall.advance
    (scaleStep scale stepValue)
    (scaleOneStepBound scale scaleNonnegative stepValue nextBound)
    (scalePath scale scaleNonnegative restPath)

record WeightedMeanGronwallData : Set where
  constructor weighted-mean-gronwall
  field
    windowHead : Weighted.WeightedValue
    windowTail : List Weighted.WeightedValue
    steps : List Gronwall.GronwallStep
    terminalEnergy : ℚ

    pathFromSelectedMinimum :
      Gronwall.GronwallPath
        (Mean.selected
          (Mean.finiteWeightedMeanValueSelection windowHead windowTail))
        steps
        terminalEnergy

open WeightedMeanGronwallData public

weightedWindow : WeightedMeanGronwallData → List Weighted.WeightedValue
weightedWindow data = windowHead data ∷ windowTail data

weightedMeanValueNonuniformGronwall :
  (data : WeightedMeanGronwallData) →
  Weighted.mass (weightedWindow data) * terminalEnergy data
  ≤ Gronwall.envelope
      (Weighted.firstMoment (weightedWindow data))
      (scaleSteps (Weighted.mass (weightedWindow data)) (steps data))
weightedMeanValueNonuniformGronwall data =
  let
    selection =
      Mean.finiteWeightedMeanValueSelection
        (windowHead data)
        (windowTail data)

    mass = Weighted.mass (weightedWindow data)

    scaledPath =
      scalePath
        mass
        (massNonnegative (weightedWindow data))
        (pathFromSelectedMinimum data)

    initialScaleCommutative :
      Mean.selected selection * mass
      ≡ mass * Mean.selected selection
    initialScaleCommutative =
      solve (Mean.selected selection ∷ mass ∷ [])

    initialScaledBound :
      mass * Mean.selected selection
      ≤ Weighted.firstMoment (weightedWindow data)
    initialScaledBound =
      subst
        (λ left →
          left ≤ Weighted.firstMoment (weightedWindow data))
        initialScaleCommutative
        (Mean.selectedTimesMassBelowMoment selection)
  in
  Gronwall.finiteNonuniformGronwall
    scaledPath
    initialScaledBound

finiteWeightedMeanValueGronwallClosed : Bool
finiteWeightedMeanValueGronwallClosed = true

finiteWeightedMeanValueGronwallClosedIsTrue :
  finiteWeightedMeanValueGronwallClosed ≡ true
finiteWeightedMeanValueGronwallClosedIsTrue = refl
