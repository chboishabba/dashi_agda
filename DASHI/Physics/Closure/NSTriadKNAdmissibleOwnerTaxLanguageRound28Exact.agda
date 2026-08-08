module DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier-Stokes Equations".
-- DOI: 10.48550/arXiv.2606.27560.
--
-- DASHI CONTRIBUTION
--
-- Make the permitted right-hand side of every physical owner estimate a type:
--
--   eta * dissipation + dataRemainder + B * integralCritical.
--
-- There is no constructor for an uncontrolled BKM, Serrin or target critical
-- supremum.  A finite list of owner estimates is aggregated exactly, retaining
-- the literal sum of viscosity coefficients.  The analytic work still has to
-- inhabit each owner estimate and prove the strict total coefficient below one.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax

record TaxEnvironment : Set where
  constructor tax-environment
  field
    dissipation : ℚ
    integralCritical : ℚ

open TaxEnvironment public

record AdmissibleOwnerEstimate (environment : TaxEnvironment) : Set where
  constructor admissible-owner-estimate
  field
    owner : Tax.TaxOwner
    positiveProduction : ℚ
    eta : ℚ
    dataRemainder : ℚ
    criticalCoefficient : ℚ

    ownerBound :
      positiveProduction
      ≤ eta * dissipation environment
        + dataRemainder
        + criticalCoefficient * integralCritical environment

open AdmissibleOwnerEstimate public

sumProduction :
  ∀ {environment} → List (AdmissibleOwnerEstimate environment) → ℚ
sumProduction [] = 0ℚ
sumProduction (estimate ∷ rest) =
  positiveProduction estimate + sumProduction rest

sumEta :
  ∀ {environment} → List (AdmissibleOwnerEstimate environment) → ℚ
sumEta [] = 0ℚ
sumEta (estimate ∷ rest) = eta estimate + sumEta rest

sumDataRemainder :
  ∀ {environment} → List (AdmissibleOwnerEstimate environment) → ℚ
sumDataRemainder [] = 0ℚ
sumDataRemainder (estimate ∷ rest) =
  dataRemainder estimate + sumDataRemainder rest

sumCriticalCoefficient :
  ∀ {environment} → List (AdmissibleOwnerEstimate environment) → ℚ
sumCriticalCoefficient [] = 0ℚ
sumCriticalCoefficient (estimate ∷ rest) =
  criticalCoefficient estimate + sumCriticalCoefficient rest

admissibleAggregateRight :
  ∀ {environment} →
  List (AdmissibleOwnerEstimate environment) → ℚ
admissibleAggregateRight {environment} estimates =
  sumEta estimates * dissipation environment
  + sumDataRemainder estimates
  + sumCriticalCoefficient estimates * integralCritical environment

aggregateOwnerEstimates :
  ∀ {environment}
    (estimates : List (AdmissibleOwnerEstimate environment)) →
  sumProduction estimates ≤ admissibleAggregateRight estimates
aggregateOwnerEstimates {environment} [] =
  subst
    (λ upper → 0ℚ ≤ upper)
    (solve
      (dissipation environment ∷ integralCritical environment ∷ []))
    ℚₚ.≤-refl
aggregateOwnerEstimates {environment} (estimate ∷ rest) =
  let
    summed :
      positiveProduction estimate + sumProduction rest
      ≤
      (eta estimate * dissipation environment
        + dataRemainder estimate
        + criticalCoefficient estimate * integralCritical environment)
      + admissibleAggregateRight rest
    summed =
      ℚₚ.+-mono-≤
        (ownerBound estimate)
        (aggregateOwnerEstimates rest)

    rightMeaning :
      (eta estimate * dissipation environment
        + dataRemainder estimate
        + criticalCoefficient estimate * integralCritical environment)
      + admissibleAggregateRight rest
      ≡
      admissibleAggregateRight (estimate ∷ rest)
    rightMeaning =
      solve
        ( eta estimate
        ∷ sumEta rest
        ∷ dissipation environment
        ∷ dataRemainder estimate
        ∷ sumDataRemainder rest
        ∷ criticalCoefficient estimate
        ∷ sumCriticalCoefficient rest
        ∷ integralCritical environment
        ∷ [])
  in
  subst
    (λ upper → sumProduction (estimate ∷ rest) ≤ upper)
    rightMeaning
    summed

record StrictAdmissibleOwnerBudget
    {environment : TaxEnvironment}
    (estimates : List (AdmissibleOwnerEstimate environment)) : Set where
  constructor strict-admissible-owner-budget
  field
    eachEtaNonnegative :
      (estimate : AdmissibleOwnerEstimate environment) →
      0ℚ ≤ eta estimate
    totalEtaStrict : sumEta estimates < 1ℚ

open StrictAdmissibleOwnerBudget public

record NineOwnerEstimateFamily (environment : TaxEnvironment) : Set where
  constructor nine-owner-estimate-family
  field
    hhGood hhBad lh hl cc com kernel tail boundary :
      AdmissibleOwnerEstimate environment

    hhGoodOwner : owner hhGood ≡ Tax.HH-good
    hhBadOwner : owner hhBad ≡ Tax.HH-bad
    lhOwner : owner lh ≡ Tax.LH
    hlOwner : owner hl ≡ Tax.HL
    ccOwner : owner cc ≡ Tax.CC
    comOwner : owner com ≡ Tax.Com
    kernelOwner : owner kernel ≡ Tax.kernel
    tailOwner : owner tail ≡ Tax.tail
    boundaryOwner : owner boundary ≡ Tax.boundary

open NineOwnerEstimateFamily public

nineOwnerList :
  ∀ {environment} →
  NineOwnerEstimateFamily environment →
  List (AdmissibleOwnerEstimate environment)
nineOwnerList family =
  hhGood family ∷ hhBad family
  ∷ lh family ∷ hl family ∷ cc family ∷ com family
  ∷ kernel family ∷ tail family ∷ boundary family ∷ []

nineOwnerAggregateBound :
  ∀ {environment} (family : NineOwnerEstimateFamily environment) →
  sumProduction (nineOwnerList family)
  ≤ admissibleAggregateRight (nineOwnerList family)
nineOwnerAggregateBound family =
  aggregateOwnerEstimates (nineOwnerList family)

admissibleOwnerTaxLanguageClosed : Bool
admissibleOwnerTaxLanguageClosed = true

finiteOwnerAggregationClosed : Bool
finiteOwnerAggregationClosed = true

physicalNineOwnerEstimatesInstantiated : Bool
physicalNineOwnerEstimatesInstantiated = false

strictPhysicalEtaMarginClosed : Bool
strictPhysicalEtaMarginClosed = false

admissibleOwnerTaxLanguageClosedIsTrue :
  admissibleOwnerTaxLanguageClosed ≡ true
admissibleOwnerTaxLanguageClosedIsTrue = refl

strictPhysicalEtaMarginClosedIsFalse :
  strictPhysicalEtaMarginClosed ≡ false
strictPhysicalEtaMarginClosedIsFalse = refl
