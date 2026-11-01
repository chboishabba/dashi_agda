module DASHI.Physics.Closure.NSTriadKNPeriodicPVHHGoodNearSmoothOwnerRound39Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
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
-- Give A3/A4 the narrow physical target suggested by Round 38/39.  After a
-- literal torus decomposition
--
--   K_T3 = chi K_hom + R_T3,
--
-- the singular near part is allowed to consume HH-good viscosity reserve,
-- while the smooth periodic correction should go only to admissible data/
-- critical remainders.  If
--
--   Near <= eta D + A_near + B_near X,
--   Smooth <= A_smooth + B_smooth X,
--
-- then this module proves
--
--   Near + Smooth
--     <= eta D + (A_near+A_smooth) + (B_near+B_smooth) X
--
-- and constructs the literal `HH-good` owner estimate.
--
-- This prevents a harmless smooth torus correction from contaminating the
-- decisive viscosity coefficient.  The physical singular-kernel and smooth
-- remainder estimates themselves remain the frontier theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner

record PeriodicPVHHGoodNearSmoothEstimate
    (environment : Owner.TaxEnvironment) : Set where
  constructor periodic-pv-hhgood-near-smooth-estimate
  field
    nearProduction smoothProduction : ℚ
    eta : ℚ
    nearDataRemainder smoothDataRemainder : ℚ
    nearCriticalCoefficient smoothCriticalCoefficient : ℚ

    nearSingularBound :
      nearProduction
      ≤ eta * Owner.dissipation environment
        + nearDataRemainder
        + nearCriticalCoefficient * Owner.integralCritical environment

    smoothPeriodicBound :
      smoothProduction
      ≤ smoothDataRemainder
        + smoothCriticalCoefficient * Owner.integralCritical environment

open PeriodicPVHHGoodNearSmoothEstimate public

totalProduction :
  ∀ {environment} →
  PeriodicPVHHGoodNearSmoothEstimate environment → ℚ
totalProduction estimate =
  nearProduction estimate + smoothProduction estimate

totalDataRemainder :
  ∀ {environment} →
  PeriodicPVHHGoodNearSmoothEstimate environment → ℚ
totalDataRemainder estimate =
  nearDataRemainder estimate + smoothDataRemainder estimate

totalCriticalCoefficient :
  ∀ {environment} →
  PeriodicPVHHGoodNearSmoothEstimate environment → ℚ
totalCriticalCoefficient estimate =
  nearCriticalCoefficient estimate + smoothCriticalCoefficient estimate

nearSmoothHHGoodAggregateBound :
  ∀ {environment}
    (estimate : PeriodicPVHHGoodNearSmoothEstimate environment) →
  totalProduction estimate
  ≤ eta estimate * Owner.dissipation environment
      + totalDataRemainder estimate
      + totalCriticalCoefficient estimate * Owner.integralCritical environment
nearSmoothHHGoodAggregateBound {environment} estimate =
  let
    summed :
      nearProduction estimate + smoothProduction estimate
      ≤
      (eta estimate * Owner.dissipation environment
        + nearDataRemainder estimate
        + nearCriticalCoefficient estimate * Owner.integralCritical environment)
      +
      (smoothDataRemainder estimate
        + smoothCriticalCoefficient estimate * Owner.integralCritical environment)
    summed = ℚP.+-mono-≤
      (nearSingularBound estimate)
      (smoothPeriodicBound estimate)

    rightMeaning :
      (eta estimate * Owner.dissipation environment
        + nearDataRemainder estimate
        + nearCriticalCoefficient estimate * Owner.integralCritical environment)
      +
      (smoothDataRemainder estimate
        + smoothCriticalCoefficient estimate * Owner.integralCritical environment)
      ≡
      eta estimate * Owner.dissipation environment
        + totalDataRemainder estimate
        + totalCriticalCoefficient estimate * Owner.integralCritical environment
    rightMeaning = solve
      ( eta estimate
      ∷ Owner.dissipation environment
      ∷ nearDataRemainder estimate
      ∷ smoothDataRemainder estimate
      ∷ nearCriticalCoefficient estimate
      ∷ smoothCriticalCoefficient estimate
      ∷ Owner.integralCritical environment
      ∷ [])
  in
  subst
    (λ upper → totalProduction estimate ≤ upper)
    rightMeaning
    summed

hhGoodOwnerEstimateFromNearSmooth :
  ∀ {environment} →
  PeriodicPVHHGoodNearSmoothEstimate environment →
  Owner.AdmissibleOwnerEstimate environment
hhGoodOwnerEstimateFromNearSmooth {environment} estimate =
  Owner.admissible-owner-estimate
    Tax.HH-good
    (totalProduction estimate)
    (eta estimate)
    (totalDataRemainder estimate)
    (totalCriticalCoefficient estimate)
    (nearSmoothHHGoodAggregateBound estimate)

hhGoodOwnerIdentity :
  ∀ {environment}
    (estimate : PeriodicPVHHGoodNearSmoothEstimate environment) →
  Owner.owner (hhGoodOwnerEstimateFromNearSmooth estimate) ≡ Tax.HH-good
hhGoodOwnerIdentity estimate = refl

periodicPVHHGoodNearSmoothOwnerReducerClosed : Bool
periodicPVHHGoodNearSmoothOwnerReducerClosed = true

physicalPeriodicPVHHGoodNearSmoothEstimateConstructed : Bool
physicalPeriodicPVHHGoodNearSmoothEstimateConstructed = false

periodicPVHHGoodNearSmoothOwnerReducerClosedIsTrue :
  periodicPVHHGoodNearSmoothOwnerReducerClosed ≡ true
periodicPVHHGoodNearSmoothOwnerReducerClosedIsTrue = refl
