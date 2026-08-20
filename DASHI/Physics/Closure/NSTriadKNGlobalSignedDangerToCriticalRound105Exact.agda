module DASHI.Physics.Closure.NSTriadKNGlobalSignedDangerToCriticalRound105Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "The Regularity of Weak Solutions of the 3D Navier-Stokes Equations
-- in B^{-1}_{infinity,infinity}".
-- Archive for Rational Mechanics and Analysis 195 (2010), 159--169.
-- DOI: 10.1007/s00205-009-0265-2.
--
-- ROUND105 / GLOBAL SIGNED DANGER -> CRITICAL SLICE
--
-- This file removes the per-cell danger-cost constructor from the shortest
-- Clay path.  A raw sample stores ONLY the signed critical production N_i and
-- dissipation D_i.  The complete interval surplus is formed first:
--
--   S = sum_i N_i + delta sum_i D_i.
--
-- Its one global positive part S_+ is the minimal nonnegative scalar payment
-- supplied by the ordered rational carrier.  If the physical trajectory proves
--
--   S_+ <= F,
--
-- then automatically
--
--   sum_i N_i <= (-delta) sum_i D_i + F.
--
-- Combined with the exact critical energy inequality this constructs the
-- existing Round104 `IntegratedSignedCriticalSlice`, retaining viscosity
-- nu+delta.  Cross-cell cancellation is preserved until the final positive-part
-- operation; no `SignedDangerCostCell`, local absolute value, or local tax is
-- required.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; -_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNGlobalSignedDangerPositivePartRound105Exact as Positive
import DASHI.Physics.Closure.NSTriadKNUniformGalerkinSignedCriticalProductionRound104Exact as Signed

record RawSignedCriticalSample : Set where
  constructor raw-signed-critical-sample
  field
    production dissipation : ℚ

open RawSignedCriticalSample public

sumProduction : List RawSignedCriticalSample → ℚ
sumProduction [] = 0ℚ
sumProduction (sample ∷ rest) = production sample + sumProduction rest

sumDissipation : List RawSignedCriticalSample → ℚ
sumDissipation [] = 0ℚ
sumDissipation (sample ∷ rest) = dissipation sample + sumDissipation rest

integratedSurplus : ℚ → List RawSignedCriticalSample → ℚ
integratedSurplus delta samples =
  sumProduction samples + delta * sumDissipation samples

globalDanger : ℚ → List RawSignedCriticalSample → ℚ
globalDanger delta samples = Positive.positivePart (integratedSurplus delta samples)

globalDangerDominatesSurplus :
  (delta : ℚ) (samples : List RawSignedCriticalSample) →
  integratedSurplus delta samples ≤ globalDanger delta samples
globalDangerDominatesSurplus delta samples =
  Positive.positivePartDominates (integratedSurplus delta samples)

record GlobalDangerCriticalEnergyWeld (delta : ℚ) : Set where
  constructor global-danger-critical-energy-weld
  field
    samples : List RawSignedCriticalSample
    viscosity initialCritical terminalCritical endpointRemainder : ℚ

    criticalEnergyInequality :
      terminalCritical + viscosity * sumDissipation samples
      ≤ initialCritical + sumProduction samples

    globalDangerPaidByEndpoint :
      globalDanger delta samples ≤ endpointRemainder

open GlobalDangerCriticalEnergyWeld public

globalSignedProductionEstimate :
  ∀ {delta} (W : GlobalDangerCriticalEnergyWeld delta) →
  sumProduction (samples W)
  ≤ (- delta) * sumDissipation (samples W) + endpointRemainder W
globalSignedProductionEstimate {delta} W =
  let
    P = sumProduction (samples W)
    D = sumDissipation (samples W)
    F = endpointRemainder W

    surplusPaid : P + delta * D ≤ F
    surplusPaid =
      ℚP.≤-trans
        (globalDangerDominatesSurplus delta (samples W))
        (globalDangerPaidByEndpoint W)

    shifted :
      (P + delta * D) + (- (delta * D))
      ≤ F + (- (delta * D))
    shifted = ℚP.+-mono-≤ surplusPaid ℚP.≤-refl

    leftMeaning : (P + delta * D) + (- (delta * D)) ≡ P
    leftMeaning = solve (P ∷ delta ∷ D ∷ [])

    rightMeaning : F + (- (delta * D)) ≡ (- delta) * D + F
    rightMeaning = solve (F ∷ delta ∷ D ∷ [])
  in
  subst
    (λ left → left ≤ (- delta) * D + F)
    leftMeaning
    (subst
      (λ right → (P + delta * D) + (- (delta * D)) ≤ right)
      rightMeaning shifted)

globalDangerBuildsSignedCriticalSlice :
  ∀ {delta} →
  GlobalDangerCriticalEnergyWeld delta →
  Signed.IntegratedSignedCriticalSlice
globalDangerBuildsSignedCriticalSlice {delta} W =
  Signed.integrated-signed-critical-slice
    (initialCritical W)
    (terminalCritical W)
    (sumDissipation (samples W))
    (sumProduction (samples W))
    (endpointRemainder W)
    (viscosity W)
    (- delta)
    (criticalEnergyInequality W)
    (globalSignedProductionEstimate W)

globalDangerRetainedViscosityIsNuPlusDelta :
  ∀ {delta} (W : GlobalDangerCriticalEnergyWeld delta) →
  Signed.retainedViscosity (globalDangerBuildsSignedCriticalSlice W)
  ≡ viscosity W + delta
globalDangerRetainedViscosityIsNuPlusDelta {delta} W =
  solve (viscosity W ∷ delta ∷ [])

round105GlobalDangerDirectCriticalCompilerClosed : Bool
round105GlobalDangerDirectCriticalCompilerClosed = true

round105LocalDangerCellConstructorRequired : Bool
round105LocalDangerCellConstructorRequired = false

-- Physical frontier: instantiate the raw samples from the literal nested
-- critical packet-flux trajectory and prove one cutoff-uniform endpoint bound
-- on `globalDanger`.  No local danger-cell theorem remains downstream.
round105PhysicalGlobalCriticalDangerBoundClosed : Bool
round105PhysicalGlobalCriticalDangerBoundClosed = false

round105GlobalDangerDirectCriticalCompilerClosedIsTrue :
  round105GlobalDangerDirectCriticalCompilerClosed ≡ true
round105GlobalDangerDirectCriticalCompilerClosedIsTrue = refl

round105LocalDangerCellConstructorRequiredIsFalse :
  round105LocalDangerCellConstructorRequired ≡ false
round105LocalDangerCellConstructorRequiredIsFalse = refl

round105PhysicalGlobalCriticalDangerBoundClosedIsFalse :
  round105PhysicalGlobalCriticalDangerBoundClosed ≡ false
round105PhysicalGlobalCriticalDangerBoundClosedIsFalse = refl
