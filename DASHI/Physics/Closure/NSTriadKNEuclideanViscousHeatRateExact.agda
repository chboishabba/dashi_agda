module DASHI.Physics.Closure.NSTriadKNEuclideanViscousHeatRateExact where

------------------------------------------------------------------------
-- A / LITERAL WHOLE-SPACE VISCOUS HEAT RATE
--
-- Fix the Bishop-real scalar used by the Euclidean resolvent:
--
--   a(xi) = nu |xi|^2.
--
-- This owner proves the exact low-frequency cube identity
--
--   a(xi)^3 ~= nu^3 (|xi|^2)^3,
--
-- so the abstract heat-cube compensation theorem is literally the desired
-- |xi|^6 payment (with the physical viscosity factor retained).
--
-- No periodic unit gap is used.  Positivity is carried only on the punctured
-- frequency region where |xi|^2 > 0.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSWholeSpaceLowFrequencyCompensationExact as Low

square : BishopReal.ℝ → BishopReal.ℝ
square x = BishopReal._*_ x x

frequencyNormSquared :
  Euclidean.R3Frequency → BishopReal.ℝ
frequencyNormSquared frequency =
  BishopReal._+_
    (square (Euclidean.x frequency))
    (BishopReal._+_
      (square (Euclidean.y frequency))
      (square (Euclidean.z frequency)))

record PositiveViscosity : Set where
  constructor positive-viscosity
  field
    viscosity : BishopReal.ℝ
    viscosityPositive :
      BishopReal._<_ BishopReal.0ℝ viscosity

open PositiveViscosity public

record PuncturedEuclideanFrequency : Set where
  constructor punctured-euclidean-frequency
  field
    frequency : Euclidean.R3Frequency
    normSquaredPositive :
      BishopReal._<_ BishopReal.0ℝ
        (frequencyNormSquared frequency)

open PuncturedEuclideanFrequency public

viscousHeatRate :
  PositiveViscosity →
  Euclidean.R3Frequency →
  BishopReal.ℝ
viscousHeatRate fluid frequency =
  BishopReal._*_
    (viscosity fluid)
    (frequencyNormSquared frequency)

viscousHeatRatePositive :
  (fluid : PositiveViscosity) →
  (point : PuncturedEuclideanFrequency) →
  BishopReal._<_ BishopReal.0ℝ
    (viscousHeatRate fluid (frequency point))
viscousHeatRatePositive fluid point =
  BishopP.posx⇒0<x
    (BishopP.posx,y⇒posx*y
      (BishopP.0<x⇒posx (viscosityPositive fluid))
      (BishopP.0<x⇒posx (normSquaredPositive point)))

cube : BishopReal.ℝ → BishopReal.ℝ
cube x =
  BishopReal._*_
    (BishopReal._*_ x x)
    x

viscosityCube : PositiveViscosity → BishopReal.ℝ
viscosityCube fluid = cube (viscosity fluid)

frequencySixthPower :
  Euclidean.R3Frequency → BishopReal.ℝ
frequencySixthPower frequency =
  cube (frequencyNormSquared frequency)

heatCubeIsViscosityCubeTimesFrequencySixth :
  (fluid : PositiveViscosity) →
  (frequency : Euclidean.R3Frequency) →
  BishopReal._≃_
    (Low.heatCube (viscousHeatRate fluid frequency))
    (BishopReal._*_
      (viscosityCube fluid)
      (frequencySixthPower frequency))
heatCubeIsViscosityCubeTimesFrequencySixth fluid frequency =
  let
    nu = viscosity fluid
    r2 = frequencyNormSquared frequency
    open BishopP.ℝ-Solver
  in
  solve 2
    (λ n r →
      (((n ⊗ r) ⊗ (n ⊗ r)) ⊗ (n ⊗ r))
      ⊜
      (((n ⊗ n) ⊗ n) ⊗ ((r ⊗ r) ⊗ r)))
    BishopP.≃-refl
    nu r2

viscosityCubePositive :
  (fluid : PositiveViscosity) →
  BishopReal.Positive (viscosityCube fluid)
viscosityCubePositive fluid =
  let p = BishopP.0<x⇒posx (viscosityPositive fluid)
  in
  BishopP.posx,y⇒posx*y
    (BishopP.posx,y⇒posx*y p p)
    p

frequencySixthPositive :
  (point : PuncturedEuclideanFrequency) →
  BishopReal.Positive
    (frequencySixthPower (frequency point))
frequencySixthPositive point =
  let p = BishopP.0<x⇒posx (normSquaredPositive point)
  in
  BishopP.posx,y⇒posx*y
    (BishopP.posx,y⇒posx*y p p)
    p

scaledFrequencyNormSquared :
  (scalar : BishopReal.ℝ) →
  (frequency : Euclidean.R3Frequency) →
  BishopReal._≃_
    (frequencyNormSquared
      (Euclidean.r3-frequency
        (BishopReal._*_ scalar (Euclidean.x frequency))
        (BishopReal._*_ scalar (Euclidean.y frequency))
        (BishopReal._*_ scalar (Euclidean.z frequency))))
    (BishopReal._*_
      (square scalar)
      (frequencyNormSquared frequency))
scaledFrequencyNormSquared scalar frequency =
  let
    x = Euclidean.x frequency
    y = Euclidean.y frequency
    z = Euclidean.z frequency
    open BishopP.ℝ-Solver
  in
  solve 4
    (λ s x' y' z' →
      ((s ⊗ x') ⊗ (s ⊗ x'))
      ⊕
      (((s ⊗ y') ⊗ (s ⊗ y'))
       ⊕ ((s ⊗ z') ⊗ (s ⊗ z')))
      ⊜
      (s ⊗ s)
      ⊗
      ((x' ⊗ x') ⊕ ((y' ⊗ y') ⊕ (z' ⊗ z'))))
    BishopP.≃-refl
    scalar x y z

viscousHeatRateUsesNoSpectralGap : Bool
viscousHeatRateUsesNoSpectralGap = true

viscousHeatRatePhysicalFormulaClosed : Bool
viscousHeatRatePhysicalFormulaClosed = true

heatCubeEqualsNuCubeFrequencySixthClosed : Bool
heatCubeEqualsNuCubeFrequencySixthClosed = true

originExcludedOnlyForReciprocal : Bool
originExcludedOnlyForReciprocal = true

clayPromotion : Bool
clayPromotion = false

viscousHeatRatePhysicalFormulaClosedIsTrue :
  viscousHeatRatePhysicalFormulaClosed ≡ true
viscousHeatRatePhysicalFormulaClosedIsTrue = refl

heatCubeEqualsNuCubeFrequencySixthClosedIsTrue :
  heatCubeEqualsNuCubeFrequencySixthClosed ≡ true
heatCubeEqualsNuCubeFrequencySixthClosedIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
