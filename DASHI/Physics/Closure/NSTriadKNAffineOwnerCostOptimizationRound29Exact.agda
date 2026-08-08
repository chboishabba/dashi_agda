module DASHI.Physics.Closure.NSTriadKNAffineOwnerCostOptimizationRound29Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Owner estimates expose symbolic affine Young-parameter costs first. Numerical
-- choices are made only after all owners have been assembled. An exact rational
-- certificate then becomes the existing strict owner budget.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Language

record AffineEtaParameter : Set where
  constructor affine-eta-parameter
  field
    etaBase etaSlope chosenParameter : ℚ

open AffineEtaParameter public

etaValue : AffineEtaParameter → ℚ
etaValue parameter =
  etaBase parameter + etaSlope parameter * chosenParameter parameter

record SymbolicOwnerCost
    (environment : Language.TaxEnvironment) : Set where
  constructor symbolic-owner-cost
  field
    owner : Tax.TaxOwner
    positiveProduction : ℚ
    etaParameter : AffineEtaParameter
    dataRemainder criticalCoefficient : ℚ
    ownerBound :
      positiveProduction
      ≤ etaValue etaParameter * Language.dissipation environment
        + dataRemainder
        + criticalCoefficient * Language.integralCritical environment

open SymbolicOwnerCost public

toAdmissibleOwnerEstimate :
  ∀ {environment} →
  SymbolicOwnerCost environment →
  Language.AdmissibleOwnerEstimate environment
toAdmissibleOwnerEstimate symbolic =
  Language.admissible-owner-estimate
    (owner symbolic)
    (positiveProduction symbolic)
    (etaValue (etaParameter symbolic))
    (dataRemainder symbolic)
    (criticalCoefficient symbolic)
    (ownerBound symbolic)

mapSymbolicOwnerCosts :
  ∀ {environment} →
  List (SymbolicOwnerCost environment) →
  List (Language.AdmissibleOwnerEstimate environment)
mapSymbolicOwnerCosts [] = []
mapSymbolicOwnerCosts (cost ∷ rest) =
  toAdmissibleOwnerEstimate cost ∷ mapSymbolicOwnerCosts rest

sumSymbolicEta :
  ∀ {environment} →
  List (SymbolicOwnerCost environment) → ℚ
sumSymbolicEta [] = 0ℚ
sumSymbolicEta (cost ∷ rest) =
  etaValue (etaParameter cost) + sumSymbolicEta rest

sumSymbolicEtaAgrees :
  ∀ {environment}
    (costs : List (SymbolicOwnerCost environment)) →
  Language.sumEta (mapSymbolicOwnerCosts costs)
  ≡ sumSymbolicEta costs
sumSymbolicEtaAgrees [] = refl
sumSymbolicEtaAgrees (cost ∷ rest)
  rewrite sumSymbolicEtaAgrees rest = refl

data AllSymbolicEtasNonnegative
    {environment : Language.TaxEnvironment} :
    List (SymbolicOwnerCost environment) → Set where
  symbolic[] : AllSymbolicEtasNonnegative []
  symbolic∷ :
    ∀ {cost rest} →
    0ℚ ≤ etaValue (etaParameter cost) →
    AllSymbolicEtasNonnegative rest →
    AllSymbolicEtasNonnegative (cost ∷ rest)

symbolicNonnegativeToAdmissible :
  ∀ {environment}
    {costs : List (SymbolicOwnerCost environment)} →
  AllSymbolicEtasNonnegative costs →
  Language.AllEtasNonnegative (mapSymbolicOwnerCosts costs)
symbolicNonnegativeToAdmissible symbolic[] = Language.allEtas[]
symbolicNonnegativeToAdmissible (symbolic∷ etaNN rest) =
  Language.allEtas∷ etaNN (symbolicNonnegativeToAdmissible rest)

record SymbolicStrictBudget
    {environment : Language.TaxEnvironment}
    (costs : List (SymbolicOwnerCost environment)) : Set where
  constructor symbolic-strict-budget
  field
    eachEtaNonnegative : AllSymbolicEtasNonnegative costs
    symbolicTotalStrict : sumSymbolicEta costs < 1ℚ
    symbolicRemainingPositive : 0ℚ < 1ℚ - sumSymbolicEta costs

open SymbolicStrictBudget public

symbolicBudgetProducesStrictAdmissibleBudget :
  ∀ {environment}
    (costs : List (SymbolicOwnerCost environment)) →
  SymbolicStrictBudget costs →
  Language.StrictAdmissibleOwnerBudget (mapSymbolicOwnerCosts costs)
symbolicBudgetProducesStrictAdmissibleBudget costs certificate =
  Language.strict-admissible-owner-budget
    (symbolicNonnegativeToAdmissible
      (eachEtaNonnegative certificate))
    (subst
      (λ total → total < 1ℚ)
      (sym (sumSymbolicEtaAgrees costs))
      (symbolicTotalStrict certificate))
    (subst
      (λ total → 0ℚ < 1ℚ - total)
      (sym (sumSymbolicEtaAgrees costs))
      (symbolicRemainingPositive certificate))
  where
  open import Relation.Binary.PropositionalEquality using (subst; sym)

affineOwnerCostOptimizationClosed : Bool
affineOwnerCostOptimizationClosed = true

physicalSymbolicOwnerCostsInstantiated : Bool
physicalSymbolicOwnerCostsInstantiated = false

affineOwnerCostOptimizationClosedIsTrue :
  affineOwnerCostOptimizationClosed ≡ true
affineOwnerCostOptimizationClosedIsTrue = refl

physicalSymbolicOwnerCostsInstantiatedIsFalse :
  physicalSymbolicOwnerCostsInstantiated ≡ false
physicalSymbolicOwnerCostsInstantiatedIsFalse = refl
