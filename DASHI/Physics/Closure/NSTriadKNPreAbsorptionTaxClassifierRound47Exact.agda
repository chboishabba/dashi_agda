module DASHI.Physics.Closure.NSTriadKNPreAbsorptionTaxClassifierRound47Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- Proceedings of the Royal Society of London. Series A 87 (1912).
-- DOI: 10.1098/rspa.1912.0086.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Make the Round-47 Com/kernel instruction executable: do not choose eta first.
-- Prove the natural pre-absorption inequality, then classify its endpoint.
--
--   Zero endpoint:
--     P <= A + B X
--       => eta = 0 exactly.
--
--   Mixed endpoint:
--     P <= x y + A, x^2 <= D, y^2 <= C X
--       => Young-soft for every epsilon > 0.
--
--   Hard endpoint:
--     P <= c D + A + B X, c > 0
--       => a hard certificate with floor c.
--
-- The mixed case reuses the actual scaled Young proof from the repository,
-- rather than encoding "soft" as a label.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNTaxKindClassificationRound46Exact as Kind
import DASHI.Physics.Closure.NSTriadKNMixedCriticalYoungSoftRound47Exact as Mixed

record ZeroCriticalPreAbsorption
    (environment : Owner.TaxEnvironment)
    (selectedOwner : Tax.TaxOwner) : Set where
  field
    production dataRemainder criticalCoefficient : ℚ
    endpointBound :
      production
      ≤ dataRemainder
        + criticalCoefficient * Owner.integralCritical environment

open ZeroCriticalPreAbsorption public

zeroEndpointOwnerEstimate :
  ∀ {environment selectedOwner} →
  ZeroCriticalPreAbsorption environment selectedOwner →
  Owner.AdmissibleOwnerEstimate environment
zeroEndpointOwnerEstimate {environment} {selectedOwner} endpoint =
  Owner.admissible-owner-estimate
    selectedOwner
    (production endpoint)
    0ℚ
    (dataRemainder endpoint)
    (criticalCoefficient endpoint)
    ownerBound
  where
  targetMeaning :
    0ℚ * Owner.dissipation environment
      + dataRemainder endpoint
      + criticalCoefficient endpoint * Owner.integralCritical environment
    ≡ dataRemainder endpoint
      + criticalCoefficient endpoint * Owner.integralCritical environment
  targetMeaning = solve
    ( Owner.dissipation environment
    ∷ dataRemainder endpoint
    ∷ criticalCoefficient endpoint
    ∷ Owner.integralCritical environment
    ∷ [])

  ownerBound =
    subst
      (production endpoint ≤_)
      (sym targetMeaning)
      (endpointBound endpoint)

zeroEndpointClassification :
  ∀ {environment selectedOwner} →
  ZeroCriticalPreAbsorption environment selectedOwner →
  Kind.TaxClassification environment selectedOwner
zeroEndpointClassification endpoint =
  Kind.zeroClassification record
    { estimate = zeroEndpointOwnerEstimate endpoint
    ; ownerExact = refl
    ; etaZero = refl
    }

mixedEndpointClassification :
  ∀ {environment selectedOwner} →
  Mixed.MixedCriticalPreAbsorption environment selectedOwner →
  Kind.TaxClassification environment selectedOwner
mixedEndpointClassification endpoint =
  Kind.youngSoftClassification
    (Mixed.mixedCriticalYoungSoftFamily endpoint)

record HardCriticalPreAbsorption
    (environment : Owner.TaxEnvironment)
    (selectedOwner : Tax.TaxOwner) : Set where
  field
    production hardCoefficient dataRemainder criticalCoefficient : ℚ
    hardCoefficientPositive : 0ℚ < hardCoefficient
    endpointBound :
      production
      ≤ hardCoefficient * Owner.dissipation environment
        + dataRemainder
        + criticalCoefficient * Owner.integralCritical environment

open HardCriticalPreAbsorption public

hardEndpointOwnerEstimate :
  ∀ {environment selectedOwner} →
  HardCriticalPreAbsorption environment selectedOwner →
  Owner.AdmissibleOwnerEstimate environment
hardEndpointOwnerEstimate {selectedOwner = selectedOwner} endpoint =
  Owner.admissible-owner-estimate
    selectedOwner
    (production endpoint)
    (hardCoefficient endpoint)
    (dataRemainder endpoint)
    (criticalCoefficient endpoint)
    (endpointBound endpoint)

hardEndpointClassification :
  ∀ {environment selectedOwner} →
  HardCriticalPreAbsorption environment selectedOwner →
  Kind.TaxClassification environment selectedOwner
hardEndpointClassification endpoint =
  Kind.hardClassification record
    { estimate = hardEndpointOwnerEstimate endpoint
    ; ownerExact = refl
    ; floor = hardCoefficient endpoint
    ; floorPositive = hardCoefficientPositive endpoint
    ; floorBelowEta = ℚP.≤-refl
    }

comZeroEndpointClassification :
  ∀ {environment} →
  ZeroCriticalPreAbsorption environment Tax.Com →
  Kind.TaxClassification environment Tax.Com
comZeroEndpointClassification = zeroEndpointClassification

comMixedEndpointClassification :
  ∀ {environment} →
  Mixed.MixedCriticalPreAbsorption environment Tax.Com →
  Kind.TaxClassification environment Tax.Com
comMixedEndpointClassification = mixedEndpointClassification

comHardEndpointClassification :
  ∀ {environment} →
  HardCriticalPreAbsorption environment Tax.Com →
  Kind.TaxClassification environment Tax.Com
comHardEndpointClassification = hardEndpointClassification

kernelZeroEndpointClassification :
  ∀ {environment} →
  ZeroCriticalPreAbsorption environment Tax.kernel →
  Kind.TaxClassification environment Tax.kernel
kernelZeroEndpointClassification = zeroEndpointClassification

kernelMixedEndpointClassification :
  ∀ {environment} →
  Mixed.MixedCriticalPreAbsorption environment Tax.kernel →
  Kind.TaxClassification environment Tax.kernel
kernelMixedEndpointClassification = mixedEndpointClassification

kernelHardEndpointClassification :
  ∀ {environment} →
  HardCriticalPreAbsorption environment Tax.kernel →
  Kind.TaxClassification environment Tax.kernel
kernelHardEndpointClassification = hardEndpointClassification

preAbsorptionEndpointDecidesTaxKind : Bool
preAbsorptionEndpointDecidesTaxKind = true

preAbsorptionEndpointDecidesTaxKindIsTrue :
  preAbsorptionEndpointDecidesTaxKind ≡ true
preAbsorptionEndpointDecidesTaxKindIsTrue = refl
