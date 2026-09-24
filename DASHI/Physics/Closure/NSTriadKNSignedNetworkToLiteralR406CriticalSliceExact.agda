module DASHI.Physics.Closure.NSTriadKNSignedNetworkToLiteralR406CriticalSliceExact where

------------------------------------------------------------------------
-- SIGNED PHASE-NETWORK BUDGET -> LITERAL R406 CRITICAL SLICE
--
-- R106/R511 preserve the signed whole-network normal form and prove
--
--   nu * P <= I + T + F.
--
-- R414 consumes the unscaled literal same-trajectory estimate
--
--   P <= a D + R406.
--
-- The missing bridge is elementary but important: for positive viscosity,
-- if the complete signed boundary/forcing budget is bounded by
--
--   nu * (a D + R406),
--
-- then constructive rational division by nu gives exactly the R414 field.
--
-- This file introduces no new Navier--Stokes estimate, positive part,
-- absolute value, shell count, or surrogate remainder.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; Positive; NonNegative; nonNegative; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNOneCancellationPaysRemainderAndCriticalRound414Exact as R414
import DASHI.Physics.Closure.NSTriadKNSignedPhaseTimeNormalFormRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNSignedNetworkBudgetCompilerRound511Exact as R511
import DASHI.Physics.Closure.NSTriadKNFrameWeightedSquareChargeRound77Exact as Reciprocal

F : C3.RealField _
F = Rational.rationalRealField

positiveScaleCancel :
  (scale left right : ℚ) →
  Positive scale →
  scale * left ≤ scale * right →
  left ≤ right
positiveScaleCancel scale left right scalePositive inequality =
  let
    inv = Reciprocal.safeRationalReciprocal scale
    invPositive = Reciprocal.safeRationalReciprocalPositive scale scalePositive
    invNN : 0ℚ ≤ inv
    invNN =
      let instance invPositiveI : Positive inv = invPositive
          instance invNonnegativeI = ℚP.pos⇒nonNeg inv
      in ℚP.nonNegative⁻¹ inv

    scaled :
      inv * (scale * left) ≤ inv * (scale * right)
    scaled =
      let instance invNNI : NonNegative inv = nonNegative invNN
      in ℚP.*-monoˡ-≤-nonNeg inv inequality

    invScale : inv * scale ≡ 1ℚ
    invScale = Reciprocal.safeRationalReciprocalTimesPositive scale scalePositive

    leftCollapse : inv * (scale * left) ≡ left
    leftCollapse =
      trans
        (solve (inv ∷ scale ∷ left ∷ []))
        (trans
          (cong (_* left) invScale)
          (ℚP.*-identityˡ left))

    rightCollapse : inv * (scale * right) ≡ right
    rightCollapse =
      trans
        (solve (inv ∷ scale ∷ right ∷ []))
        (trans
          (cong (_* right) invScale)
          (ℚP.*-identityˡ right))
  in
  subst
    (_≤ right)
    leftCollapse
    (subst
      (λ upper → inv * (scale * left) ≤ upper)
      rightCollapse
      scaled)

signedNetworkBudgetPaysUnscaledTarget :
  (N : R106.CommonViscositySignedPhaseNetwork) →
  (B : R511.SignedNetworkBudget N) →
  Positive (R106.viscosity N) →
  (target : ℚ) →
  R511.initialBudget B + R511.terminalBudget B + R511.forcingBudget B
    ≤ R106.viscosity N * target →
  R106.sumIntegratedCriticalProduction (R106.cells N) ≤ target
signedNetworkBudgetPaysUnscaledTarget N B viscosityPositive target budgetToTarget =
  positiveScaleCancel
    (R106.viscosity N)
    (R106.sumIntegratedCriticalProduction (R106.cells N))
    target
    viscosityPositive
    (ℚP.≤-trans
      (R511.signedNetworkBudgetPaysWeightedCriticalProduction B)
      budgetToTarget)

module LiteralR406SignedNetwork
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Unified = R414.Unified
    Time initialTime integrateTo DerivativeOf

  record SignedNetworkLiteralPayment
      (N : R106.CommonViscositySignedPhaseNetwork)
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T)
      (terminal : Time)
      (cutoff : Nat)
      (integratedSignedProduction criticalDissipation absorbedCoefficient : ℚ)
      : Set where
    field
      viscosityPositive : Positive (R106.viscosity N)
      budget : R511.SignedNetworkBudget N

      productionSameObject :
        R106.sumIntegratedCriticalProduction (R106.cells N)
        ≡ integratedSignedProduction

      signedBudgetPaysScaledLiteralTarget :
        R511.initialBudget budget
          + R511.terminalBudget budget
          + R511.forcingBudget budget
        ≤ R106.viscosity N
          * (absorbedCoefficient * criticalDissipation
            + Unified.literalRemainderIntegral T R cutoff terminal)

  open SignedNetworkLiteralPayment public

  signedNetworkPaysLiteralR406Production :
    ∀ {N T R terminal cutoff production dissipation absorbed} →
    SignedNetworkLiteralPayment
      N T R terminal cutoff production dissipation absorbed →
    production
    ≤ absorbed * dissipation
      + Unified.literalRemainderIntegral T R cutoff terminal
  signedNetworkPaysLiteralR406Production
      {N} {T} {R} {terminal} {cutoff}
      {production} {dissipation} {absorbed} P =
    subst
      (λ left →
        left
        ≤ absorbed * dissipation
          + Unified.literalRemainderIntegral T R cutoff terminal)
      (productionSameObject P)
      (signedNetworkBudgetPaysUnscaledTarget
        N
        (budget P)
        (viscosityPositive P)
        (absorbed * dissipation
          + Unified.literalRemainderIntegral T R cutoff terminal)
        (signedBudgetPaysScaledLiteralTarget P))

  signedNetworkBuildsLiteralCriticalSlice :
    ∀ {N T R terminal cutoff}
      (initialCritical terminalCritical criticalDissipation
       integratedSignedProduction viscousCoefficient absorbedCoefficient : ℚ) →
    terminalCritical + viscousCoefficient * criticalDissipation
      ≤ initialCritical + integratedSignedProduction →
    SignedNetworkLiteralPayment
      N T R terminal cutoff
      integratedSignedProduction criticalDissipation absorbedCoefficient →
    Unified.CriticalSliceOnLiteralR406 T R terminal cutoff
  signedNetworkBuildsLiteralCriticalSlice
      initialCritical terminalCritical criticalDissipation
      integratedSignedProduction viscousCoefficient absorbedCoefficient
      energy P =
    record
      { Unified.initialCritical = initialCritical
      ; Unified.terminalCritical = terminalCritical
      ; Unified.criticalDissipation = criticalDissipation
      ; Unified.integratedSignedProduction = integratedSignedProduction
      ; Unified.viscousCoefficient = viscousCoefficient
      ; Unified.absorbedCoefficient = absorbedCoefficient
      ; Unified.criticalEnergyInequality = energy
      ; Unified.signedProductionEstimateByLiteralRemainder =
          signedNetworkPaysLiteralR406Production P
      }
