module DASHI.Physics.Closure.NSTriadKNNineOwnerResourceReserveRound33Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- Connect the Round-32 product resource lattice to the repository's literal
-- nine-owner estimate family.  Each owner contributes exactly
--
--   (eta_i, A_i, B_i, 0),
--
-- and finite aggregation agrees coordinatewise with the existing owner sums.
-- In particular the forbidden continuation coordinate stays zero.
--
-- A StrictAdmissibleOwnerBudget then yields the explicit reserve
--
--   delta_NS = 1 - sum_i eta_i,
--
-- together with both
--
--   delta_NS > 0
--   sum_i eta_i + delta_NS = 1.
--
-- This closes the resource-valuation and robustness-slack algebra on the
-- actual nine-owner type.  It does not construct any of the nine physical
-- estimates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _<_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNResourceLatticeRound32Exact as Resource

zeroResource : Resource.ResourceVector
zeroResource =
  Resource.resource-vector 0ℚ 0ℚ 0ℚ 0ℚ

ownerResource :
  ∀ {environment} →
  Owner.AdmissibleOwnerEstimate environment →
  Resource.ResourceVector
ownerResource estimate =
  Resource.resource-vector
    (Owner.eta estimate)
    (Owner.dataRemainder estimate)
    (Owner.criticalCoefficient estimate)
    0ℚ

sumOwnerResources :
  ∀ {environment} →
  List (Owner.AdmissibleOwnerEstimate environment) →
  Resource.ResourceVector
sumOwnerResources [] = zeroResource
sumOwnerResources (estimate ∷ rest) =
  Resource._⊞_ (ownerResource estimate) (sumOwnerResources rest)

sumOwnerResourceEtaExact :
  ∀ {environment}
    (estimates : List (Owner.AdmissibleOwnerEstimate environment)) →
  Resource.dissipationCoordinate (sumOwnerResources estimates)
  ≡ Owner.sumEta estimates
sumOwnerResourceEtaExact [] = refl
sumOwnerResourceEtaExact (estimate ∷ rest) =
  cong₂ _+_ refl (sumOwnerResourceEtaExact rest)

sumOwnerResourceDataExact :
  ∀ {environment}
    (estimates : List (Owner.AdmissibleOwnerEstimate environment)) →
  Resource.dataCoordinate (sumOwnerResources estimates)
  ≡ Owner.sumDataRemainder estimates
sumOwnerResourceDataExact [] = refl
sumOwnerResourceDataExact (estimate ∷ rest) =
  cong₂ _+_ refl (sumOwnerResourceDataExact rest)

sumOwnerResourceCriticalExact :
  ∀ {environment}
    (estimates : List (Owner.AdmissibleOwnerEstimate environment)) →
  Resource.criticalCoordinate (sumOwnerResources estimates)
  ≡ Owner.sumCriticalCoefficient estimates
sumOwnerResourceCriticalExact [] = refl
sumOwnerResourceCriticalExact (estimate ∷ rest) =
  cong₂ _+_ refl (sumOwnerResourceCriticalExact rest)

sumOwnerResourceForbiddenZero :
  ∀ {environment}
    (estimates : List (Owner.AdmissibleOwnerEstimate environment)) →
  Resource.forbiddenCoordinate (sumOwnerResources estimates) ≡ 0ℚ
sumOwnerResourceForbiddenZero [] = refl
sumOwnerResourceForbiddenZero (estimate ∷ rest) =
  trans
    (cong₂ _+_ refl (sumOwnerResourceForbiddenZero rest))
    (solve [])

nineOwnerResource :
  ∀ {environment} →
  Owner.NineOwnerEstimateFamily environment →
  Resource.ResourceVector
nineOwnerResource family =
  sumOwnerResources (Owner.nineOwnerList family)

nineOwnerResourceEtaExact :
  ∀ {environment}
    (family : Owner.NineOwnerEstimateFamily environment) →
  Resource.dissipationCoordinate (nineOwnerResource family)
  ≡ Owner.sumEta (Owner.nineOwnerList family)
nineOwnerResourceEtaExact family =
  sumOwnerResourceEtaExact (Owner.nineOwnerList family)

nineOwnerResourceDataExact :
  ∀ {environment}
    (family : Owner.NineOwnerEstimateFamily environment) →
  Resource.dataCoordinate (nineOwnerResource family)
  ≡ Owner.sumDataRemainder (Owner.nineOwnerList family)
nineOwnerResourceDataExact family =
  sumOwnerResourceDataExact (Owner.nineOwnerList family)

nineOwnerResourceCriticalExact :
  ∀ {environment}
    (family : Owner.NineOwnerEstimateFamily environment) →
  Resource.criticalCoordinate (nineOwnerResource family)
  ≡ Owner.sumCriticalCoefficient (Owner.nineOwnerList family)
nineOwnerResourceCriticalExact family =
  sumOwnerResourceCriticalExact (Owner.nineOwnerList family)

nineOwnerResourceForbiddenZero :
  ∀ {environment}
    (family : Owner.NineOwnerEstimateFamily environment) →
  Resource.forbiddenCoordinate (nineOwnerResource family) ≡ 0ℚ
nineOwnerResourceForbiddenZero family =
  sumOwnerResourceForbiddenZero (Owner.nineOwnerList family)

nineOwnerViscosityReserve :
  ∀ {environment} →
  Owner.NineOwnerEstimateFamily environment → ℚ
nineOwnerViscosityReserve family =
  1ℚ - Resource.dissipationCoordinate (nineOwnerResource family)

nineOwnerResourceReserveIdentity :
  ∀ {environment}
    (family : Owner.NineOwnerEstimateFamily environment) →
  Resource.dissipationCoordinate (nineOwnerResource family)
    + nineOwnerViscosityReserve family
  ≡ 1ℚ
nineOwnerResourceReserveIdentity family =
  solve
    (Resource.dissipationCoordinate (nineOwnerResource family) ∷ [])

nineOwnerResourceReservePositive :
  ∀ {environment}
    (family : Owner.NineOwnerEstimateFamily environment) →
  Owner.StrictAdmissibleOwnerBudget (Owner.nineOwnerList family) →
  0ℚ < nineOwnerViscosityReserve family
nineOwnerResourceReservePositive family budget =
  subst
    (λ total → 0ℚ < 1ℚ - total)
    (sym (nineOwnerResourceEtaExact family))
    (Owner.remainingViscosityPositive budget)

record NineOwnerResourceCertificate
    {environment}
    (family : Owner.NineOwnerEstimateFamily environment) : Set where
  constructor nine-owner-resource-certificate
  field
    strictBudget :
      Owner.StrictAdmissibleOwnerBudget (Owner.nineOwnerList family)

open NineOwnerResourceCertificate public

certificateReservePositive :
  ∀ {environment} {family : Owner.NineOwnerEstimateFamily environment} →
  NineOwnerResourceCertificate family →
  0ℚ < nineOwnerViscosityReserve family
certificateReservePositive {family = family} certificate =
  nineOwnerResourceReservePositive family (strictBudget certificate)

certificateReserveIdentity :
  ∀ {environment} {family : Owner.NineOwnerEstimateFamily environment} →
  NineOwnerResourceCertificate family →
  Resource.dissipationCoordinate (nineOwnerResource family)
    + nineOwnerViscosityReserve family
  ≡ 1ℚ
certificateReserveIdentity {family = family} certificate =
  nineOwnerResourceReserveIdentity family

nineOwnerResourceValuationClosed : Bool
nineOwnerResourceValuationClosed = true

explicitViscosityReserveAlgebraClosed : Bool
explicitViscosityReserveAlgebraClosed = true

physicalNineOwnerResourceCertificateConstructed : Bool
physicalNineOwnerResourceCertificateConstructed = false

nineOwnerResourceValuationClosedIsTrue :
  nineOwnerResourceValuationClosed ≡ true
nineOwnerResourceValuationClosedIsTrue = refl

explicitViscosityReserveAlgebraClosedIsTrue :
  explicitViscosityReserveAlgebraClosed ≡ true
explicitViscosityReserveAlgebraClosedIsTrue = refl

physicalNineOwnerResourceCertificateConstructedIsFalse :
  physicalNineOwnerResourceCertificateConstructed ≡ false
physicalNineOwnerResourceCertificateConstructedIsFalse = refl
