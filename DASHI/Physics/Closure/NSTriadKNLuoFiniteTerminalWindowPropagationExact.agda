module DASHI.Physics.Closure.NSTriadKNLuoFiniteTerminalWindowPropagationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Thomas Hakon Gronwall.
-- Result: finite nonuniform Gronwall and variation of constants.
-- DOI: not assigned to this repository-specialised finite induction.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Finish the finite terminal-window lane in division-free form.  Weighted
-- mean-value selection and the proof-relevant nonuniform recurrence first give
-- an exact variation-of-constants envelope.  Pointwise growth and forcing
-- caps are then propagated by induction to the explicit bound
--
--   M E_N <= B^n firstMoment + F sum_{j<n} B^j,
--
-- where B=1+a.  Neither the terminal estimate nor the product/forcing bounds
-- are stored as final fields.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteWeightedJensenExact as Weighted
import DASHI.Physics.Closure.NSTriadKNLuoFiniteWeightedMeanValueGronwallExact as MeanGronwall
import DASHI.Physics.Closure.NSTriadKNLuoFiniteNonuniformGronwallExact as Gronwall
import DASHI.Physics.Closure.NSTriadKNLuoFiniteNonuniformGronwallProductExact as Product
import DASHI.Physics.Closure.NSTriadKNLuoFiniteNonuniformGronwallVariationExact as Variation

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

capPower : ℚ → Nat → ℚ
capPower growthCap zero = 1ℚ
capPower growthCap (suc n) =
  (1ℚ + growthCap) * capPower growthCap n

capGeometricPrefix : ℚ → Nat → ℚ
capGeometricPrefix growthCap zero = 0ℚ
capGeometricPrefix growthCap (suc n) =
  capPower growthCap n + capGeometricPrefix growthCap n

capPowerNonnegative :
  (growthCap : ℚ) →
  0ℚ ≤ growthCap →
  (n : Nat) →
  0ℚ ≤ capPower growthCap n
capPowerNonnegative growthCap growthCapNonnegative zero =
  Gronwall.oneNonnegative
capPowerNonnegative growthCap growthCapNonnegative (suc n) =
  let
    factorNonnegative =
      L2.addNonnegative Gronwall.oneNonnegative growthCapNonnegative
    restNonnegative = capPowerNonnegative growthCap growthCapNonnegative n
    instance
      factorIsNonnegative = nonNegative factorNonnegative
      restIsNonnegative = nonNegative restNonnegative
      productIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (1ℚ + growthCap) (capPower growthCap n)
  in
  ℚₚ.nonNegative⁻¹
    ((1ℚ + growthCap) * capPower growthCap n)

stepProductNonnegative :
  (steps : List Gronwall.GronwallStep) →
  0ℚ ≤ Product.growthProduct steps
stepProductNonnegative [] = Gronwall.oneNonnegative
stepProductNonnegative (stepValue ∷ steps) =
  let
    factorNonnegative = Gronwall.onePlusGrowthNonnegative stepValue
    restNonnegative = stepProductNonnegative steps
    instance
      factorIsNonnegative = nonNegative factorNonnegative
      restIsNonnegative = nonNegative restNonnegative
      productIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (1ℚ + Gronwall.growth stepValue)
          (Product.growthProduct steps)
  in
  ℚₚ.nonNegative⁻¹
    ((1ℚ + Gronwall.growth stepValue)
      * Product.growthProduct steps)

data UniformStepBounds
    (growthCap forcingCap : ℚ) :
    List Gronwall.GronwallStep → Set where
  empty : UniformStepBounds growthCap forcingCap []

  prepend :
    ∀ {stepValue steps} →
    Gronwall.growth stepValue ≤ growthCap →
    0ℚ ≤ Gronwall.forcing stepValue →
    Gronwall.forcing stepValue ≤ forcingCap →
    UniformStepBounds growthCap forcingCap steps →
    UniformStepBounds growthCap forcingCap (stepValue ∷ steps)

growthProductBelowCapPower :
  ∀ {growthCap forcingCap steps} →
  0ℚ ≤ growthCap →
  UniformStepBounds growthCap forcingCap steps →
  Product.growthProduct steps
  ≤ capPower growthCap (listLength steps)
growthProductBelowCapPower growthCapNonnegative empty = ℚₚ.≤-refl
growthProductBelowCapPower
  {growthCap} growthCapNonnegative
  (prepend {stepValue} {steps}
    growthBelow forcingNonnegative forcingBelow restBounds) =
  let
    restProductNonnegative = stepProductNonnegative steps
    capFactorNonnegative =
      L2.addNonnegative Gronwall.oneNonnegative growthCapNonnegative

    factorBelow :
      1ℚ + Gronwall.growth stepValue ≤ 1ℚ + growthCap
    factorBelow = ℚₚ.+-mono-≤ ℚₚ.≤-refl growthBelow

    first :
      (1ℚ + Gronwall.growth stepValue)
        * Product.growthProduct steps
      ≤ (1ℚ + growthCap) * Product.growthProduct steps
    first =
      let instance restIsNonnegative =
        nonNegative restProductNonnegative
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (Product.growthProduct steps) factorBelow

    second :
      (1ℚ + growthCap) * Product.growthProduct steps
      ≤ (1ℚ + growthCap)
          * capPower growthCap (listLength steps)
    second =
      let instance capFactorIsNonnegative =
        nonNegative capFactorNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (1ℚ + growthCap)
        (growthProductBelowCapPower growthCapNonnegative restBounds)
  in
  ℚₚ.≤-trans first second

forcingConvolutionBelowCapGeometric :
  ∀ {growthCap forcingCap steps} →
  0ℚ ≤ growthCap →
  0ℚ ≤ forcingCap →
  UniformStepBounds growthCap forcingCap steps →
  Variation.forcingConvolution steps
  ≤ forcingCap * capGeometricPrefix growthCap (listLength steps)
forcingConvolutionBelowCapGeometric
  growthCapNonnegative forcingCapNonnegative empty = ℚₚ.≤-refl
forcingConvolutionBelowCapGeometric
  {growthCap} {forcingCap}
  growthCapNonnegative forcingCapNonnegative
  (prepend {stepValue} {steps}
    growthBelow forcingNonnegative forcingBelow restBounds) =
  let
    productBound =
      growthProductBelowCapPower growthCapNonnegative restBounds
    capPowerNonneg =
      capPowerNonnegative growthCap growthCapNonnegative (listLength steps)

    firstProduct :
      Product.growthProduct steps * Gronwall.forcing stepValue
      ≤ capPower growthCap (listLength steps)
          * Gronwall.forcing stepValue
    firstProduct =
      let instance forcingIsNonnegative = nonNegative forcingNonnegative
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (Gronwall.forcing stepValue) productBound

    secondProduct :
      capPower growthCap (listLength steps)
          * Gronwall.forcing stepValue
      ≤ capPower growthCap (listLength steps) * forcingCap
    secondProduct =
      let instance capPowerIsNonnegative = nonNegative capPowerNonneg
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (capPower growthCap (listLength steps)) forcingBelow

    headBound = ℚₚ.≤-trans firstProduct secondProduct
    tailBound =
      forcingConvolutionBelowCapGeometric
        growthCapNonnegative forcingCapNonnegative restBounds

    summed :
      Product.growthProduct steps * Gronwall.forcing stepValue
        + Variation.forcingConvolution steps
      ≤ capPower growthCap (listLength steps) * forcingCap
        + forcingCap
            * capGeometricPrefix growthCap (listLength steps)
    summed = ℚₚ.+-mono-≤ headBound tailBound

    targetMeaning :
      capPower growthCap (listLength steps) * forcingCap
        + forcingCap
            * capGeometricPrefix growthCap (listLength steps)
      ≡ forcingCap
          * capGeometricPrefix growthCap (suc (listLength steps))
    targetMeaning =
      solve
        ( capPower growthCap (listLength steps)
        ∷ forcingCap
        ∷ capGeometricPrefix growthCap (listLength steps)
        ∷ []
        )
  in
  subst
    (λ upper →
      Variation.forcingConvolution (stepValue ∷ steps) ≤ upper)
    targetMeaning
    summed

record FiniteTerminalWindowPropagationData : Set₁ where
  field
    meanValuePath : MeanGronwall.WeightedMeanGronwallData
    growthCap forcingCap : ℚ
    growthCapNonnegative : 0ℚ ≤ growthCap
    forcingCapNonnegative : 0ℚ ≤ forcingCap

    firstMomentNonnegative :
      0ℚ ≤ Weighted.firstMoment
        (MeanGronwall.weightedWindow meanValuePath)

    uniformScaledStepBounds :
      UniformStepBounds growthCap forcingCap
        (MeanGronwall.scaleSteps
          (Weighted.mass (MeanGronwall.weightedWindow meanValuePath))
          (MeanGronwall.steps meanValuePath))

open FiniteTerminalWindowPropagationData public

weightedTerminalVariationBound :
  (data : FiniteTerminalWindowPropagationData) →
  Weighted.mass
      (MeanGronwall.weightedWindow (meanValuePath data))
    * MeanGronwall.terminalEnergy (meanValuePath data)
  ≤ Variation.explicitEnvelope
      (Weighted.firstMoment
        (MeanGronwall.weightedWindow (meanValuePath data)))
      (MeanGronwall.scaleSteps
        (Weighted.mass
          (MeanGronwall.weightedWindow (meanValuePath data)))
        (MeanGronwall.steps (meanValuePath data)))
weightedTerminalVariationBound data =
  let
    path = meanValuePath data
    scaledSteps =
      MeanGronwall.scaleSteps
        (Weighted.mass (MeanGronwall.weightedWindow path))
        (MeanGronwall.steps path)
  in
  subst
    (λ upper →
      Weighted.mass (MeanGronwall.weightedWindow path)
        * MeanGronwall.terminalEnergy path
      ≤ upper)
    (Variation.envelopeVariationIdentity
      (Weighted.firstMoment (MeanGronwall.weightedWindow path))
      scaledSteps)
    (MeanGronwall.weightedMeanValueNonuniformGronwall path)

weightedTerminalUniformBound :
  (data : FiniteTerminalWindowPropagationData) →
  let
    path = meanValuePath data
    scaledSteps =
      MeanGronwall.scaleSteps
        (Weighted.mass (MeanGronwall.weightedWindow path))
        (MeanGronwall.steps path)
  in
  Weighted.mass (MeanGronwall.weightedWindow path)
      * MeanGronwall.terminalEnergy path
  ≤ capPower (growthCap data) (listLength scaledSteps)
      * Weighted.firstMoment (MeanGronwall.weightedWindow path)
    + forcingCap data
      * capGeometricPrefix (growthCap data) (listLength scaledSteps)
weightedTerminalUniformBound data =
  let
    path = meanValuePath data
    scaledSteps =
      MeanGronwall.scaleSteps
        (Weighted.mass (MeanGronwall.weightedWindow path))
        (MeanGronwall.steps path)
    firstMoment = Weighted.firstMoment (MeanGronwall.weightedWindow path)

    productBound =
      growthProductBelowCapPower
        (growthCapNonnegative data)
        (uniformScaledStepBounds data)

    productScaled :
      Product.growthProduct scaledSteps * firstMoment
      ≤ capPower (growthCap data) (listLength scaledSteps) * firstMoment
    productScaled =
      let instance momentIsNonnegative =
        nonNegative (firstMomentNonnegative data)
      in
      ℚₚ.*-monoʳ-≤-nonNeg firstMoment productBound

    forcingBound =
      forcingConvolutionBelowCapGeometric
        (growthCapNonnegative data)
        (forcingCapNonnegative data)
        (uniformScaledStepBounds data)

    envelopeBound :
      Variation.explicitEnvelope firstMoment scaledSteps
      ≤ capPower (growthCap data) (listLength scaledSteps) * firstMoment
        + forcingCap data
          * capGeometricPrefix (growthCap data) (listLength scaledSteps)
    envelopeBound = ℚₚ.+-mono-≤ productScaled forcingBound
  in
  ℚₚ.≤-trans (weightedTerminalVariationBound data) envelopeBound
