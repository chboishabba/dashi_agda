module DASHI.Physics.Closure.NSTriadKNIsotropicPressureEnstrophyStrainCriterionRound78Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Dhawal Buaria; Alain Pumir.
-- Title: "Role of pressure in generation of intense velocity gradients in
-- turbulent flows".
-- DOI: 10.48550/arXiv.2308.03902.
--
-- ROUND78 / LOCAL ISOTROPIC PRESSURE SIGN
--
-- With enstrophy Omega=|omega|^2 and strain intensity Sigma=2 S:S,
-- incompressibility and the pressure Poisson equation give
--
--   tr H = (Omega-Sigma)/2,
--   H^I = (tr H/3) I,
--
-- hence
--
--   omega^T H^I omega = Omega (Omega-Sigma) / 6.
--
-- This file formalizes the scalar consequence used by the B2 pressure gate:
-- whenever 0<=Omega and Sigma<=Omega, the isotropic contraction is
-- nonnegative.  Since the stretching-acceleration equation contains
-- - omega^T H omega, that branch is locally depleting.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _/_; _+_; _*_; _-_; -_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary.Decidable.Core using (toWitness)

oneSixth : ℚ
oneSixth = Int.+ 1 / 6

oneSixthNonnegative : 0ℚ ≤ oneSixth
oneSixthNonnegative = toWitness {a? = 0ℚ ≤? oneSixth} _

isotropicPressureContraction : ℚ → ℚ → ℚ
isotropicPressureContraction enstrophy strainIntensity =
  oneSixth * enstrophy * (enstrophy - strainIntensity)

differenceNonnegative : ∀ {lower upper : ℚ} →
  lower ≤ upper → 0ℚ ≤ upper - lower
differenceNonnegative {lower} {upper} lower≤upper =
  let
    shifted : lower + (- lower) ≤ upper + (- lower)
    shifted = ℚP.+-monoʳ-≤ (- lower) lower≤upper
    leftZero : lower + (- lower) ≡ 0ℚ
    leftZero = solve (lower ∷ [])
  in
  subst
    (λ left → left ≤ upper - lower)
    leftZero
    shifted

isotropicPressureDepletingWhenEnstrophyDominatesStrain :
  ∀ enstrophy strainIntensity →
  0ℚ ≤ enstrophy →
  strainIntensity ≤ enstrophy →
  0ℚ ≤ isotropicPressureContraction enstrophy strainIntensity
isotropicPressureDepletingWhenEnstrophyDominatesStrain
    enstrophy strainIntensity enstrophyNN strain≤enstrophy =
  let
    gapNN : 0ℚ ≤ enstrophy - strainIntensity
    gapNN = differenceNonnegative strain≤enstrophy

    coefficientTimesEnstrophyNN :
      0ℚ ≤ oneSixth * enstrophy
    coefficientTimesEnstrophyNN =
      ℚP.0≤*0≤ oneSixthNonnegative enstrophyNN
  in
  ℚP.0≤*0≤ coefficientTimesEnstrophyNN gapNN

round78IsotropicPressureContractionExactFormulaConstructed : Bool
round78IsotropicPressureContractionExactFormulaConstructed = true

round78EnstrophyDominatesStrainImpliesLocalIsotropicDepletion : Bool
round78EnstrophyDominatesStrainImpliesLocalIsotropicDepletion = true

round78SelectedCriticalEventsKnownToSatisfyEnstrophyDominatesStrain : Bool
round78SelectedCriticalEventsKnownToSatisfyEnstrophyDominatesStrain = false

round78EnstrophyDominatesStrainImpliesLocalIsotropicDepletionIsTrue :
  round78EnstrophyDominatesStrainImpliesLocalIsotropicDepletion ≡ true
round78EnstrophyDominatesStrainImpliesLocalIsotropicDepletionIsTrue = refl
