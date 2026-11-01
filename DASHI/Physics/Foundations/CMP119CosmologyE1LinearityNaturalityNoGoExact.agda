{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyE1LinearityNaturalityNoGoExact where

------------------------------------------------------------------------
-- E1 MINIMALITY NO-GO.
--
-- Round142's `FirstVariationLinearity` is deliberately only linearity in the
-- function being differentiated.  It contains no chain rule or compatibility
-- between a configuration action and a tangent action.
--
-- This tiny exact countermodel shows that even an invariant potential plus a
-- valid FirstVariationLinearity calculus does NOT force marked derivative
-- covariance.  Therefore the remaining R144/B4 naturality theorem is genuine
-- information and cannot be compiled from Round142 linearity alone.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; +-identityˡ)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Physics.Foundations.CMP119AntigravityRealStrictSignExact as Strict
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionFirstVariationRound142Exact as D1

Action Configuration Tangent : Set
Action = Bool
Configuration = ⊤
Tangent = Bool

actConfiguration : Action → Configuration → Configuration
actConfiguration _ tt = tt

actTangent : Action → Tangent → Tangent
actTangent false tangent = tangent
actTangent true false = true
actTangent true true = false

potential : Configuration → ℝ
potential _ = 1ℝ

potentialInvariant : ∀ action configuration →
  potential (actConfiguration action configuration) ≡ potential configuration
potentialInvariant action tt = refl

counterFirstVariation :
  (Configuration → ℝ) → Configuration → Tangent → ℝ
counterFirstVariation f tt false = 0ℝ
counterFirstVariation f tt true = f tt

counterCalculus : D1.FirstVariationLinearity Configuration Tangent
counterCalculus = record
  { D1.FirstVariationLinearity.firstVariation = counterFirstVariation
  ; D1.FirstVariationLinearity.firstVariationCong =
      λ f g pointwise tt tangent → firstVariationCong tangent pointwise
  ; D1.FirstVariationLinearity.zeroFirstVariation =
      λ tt tangent → zeroD1 tangent
  ; D1.FirstVariationLinearity.addFirstVariation =
      λ f g tt tangent → addD1 f g tangent
  }
  where
  firstVariationCong :
    ∀ {f g : Configuration → ℝ} →
    (tangent : Tangent) →
    (∀ x → f x ≡ g x) →
    counterFirstVariation f tt tangent ≡ counterFirstVariation g tt tangent
  firstVariationCong false pointwise = refl
  firstVariationCong true pointwise = pointwise tt

  zeroD1 :
    ∀ tangent →
    counterFirstVariation (λ _ → 0ℝ) tt tangent ≡ 0ℝ
  zeroD1 false = refl
  zeroD1 true = refl

  addD1 :
    ∀ f g tangent →
    counterFirstVariation (λ x → f x +ℝ g x) tt tangent
    ≡ counterFirstVariation f tt tangent +ℝ counterFirstVariation g tt tangent
  addD1 f g false = sym (+-identityˡ 0ℝ)
  addD1 f g true = refl

DerivativeNaturality : Set
DerivativeNaturality =
  ∀ action configuration tangent →
  D1.firstVariation counterCalculus potential
    (actConfiguration action configuration)
    (actTangent action tangent)
  ≡
  D1.firstVariation counterCalculus potential configuration tangent

naturalityAtFlipTrueForcesZeroEqualsOne :
  DerivativeNaturality → 0ℝ ≡ 1ℝ
naturalityAtFlipTrueForcesZeroEqualsOne naturality =
  naturality true tt true

countermodelRejectsDerivativeNaturality :
  Strict.RealStrictSignLaws →
  DerivativeNaturality →
  Strict.Empty
countermodelRejectsDerivativeNaturality strict naturality =
  Strict.zeroNotOne strict
    (naturalityAtFlipTrueForcesZeroEqualsOne naturality)

firstVariationLinearityDoesNotImplyActionNaturality : Bool
firstVariationLinearityDoesNotImplyActionNaturality = true

invariantPotentialDoesNotForceMarkedDerivativeCovariance : Bool
invariantPotentialDoesNotForceMarkedDerivativeCovariance = true

e1DerivativeNaturalityRemainsProofBearing : Bool
e1DerivativeNaturalityRemainsProofBearing = true
