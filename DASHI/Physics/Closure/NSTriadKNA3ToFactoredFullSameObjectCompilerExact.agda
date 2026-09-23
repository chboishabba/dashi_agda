{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNA3ToFactoredFullSameObjectCompilerExact where

------------------------------------------------------------------------
-- A3 -> LITERAL FACTORED-FULL SAME-OBJECT COMPILER
--
-- R557/R572 already own the weighted R406 endpoint/diagonal consumer:
--
--   2 * integral R406
--     = integral FactoredFull
--       - integral SelfGram
--       - integral SelfFluxTangent.
--
-- R490/A3 owns a different theorem-bearing carrier: a finite family of
-- fixed-output signed pair-difference payments C_k <= B_k, with exact
-- cardinality-free summation
--
--   sum_k C_k <= sum_k B_k.
--
-- This module isolates the ONLY representation theorem needed to feed A3 into
-- the existing weighted consumer without pretending that the unweighted
-- covariance scalar is definitionally the R406 remainder:
--
--   FactoredFull_N(t) = 4 * sum_k C_k(t).
--
-- Once that same-object equality is supplied, the pointwise and integrated
-- FactoredFull budget are compiler-owned.  No new nonlinear estimate appears.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNLiveIntegratedDiagonalReducedNormalFormRound557Exact as R557
import DASHI.Physics.Closure.NSTriadKNLiteralFactoredFullSpacetimeBudgetRound567Exact as R567
import DASHI.Physics.Closure.NSTriadKNSignedRateVectorPaymentToR503Exact as A3

F : C3.RealField _
F = Rational.rationalRealField

module Compile
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (integration : R495.IntegrationTransportAuthority Time integrateTo)
    (orderIntegration : A3.IntegrationOrderAuthority Time integrateTo) where

  module Dyn = R240.PhysicalNSDynamics
    Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Live = R557.LiveIntegrated
    Time initialTime integrateTo DerivativeOf integration
  module Local = A3.LiveA3
    Time initialTime integrateTo DerivativeOf
  module Global = A3.GlobalCompiler
    Time initialTime integrateTo DerivativeOf integration
  module FactoredBudget = R567.ExactFactoredBudget
    Time initialTime integrateTo DerivativeOf integration

  record A3FactoredFullSameObjectProducer
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      familyAt :
        (cutoff : Nat) (time : Time) →
        Local.CanonicalLivePaymentFamily T R cutoff time

      -- Exact representation weld.  This is deliberately equality, not an
      -- estimate: all nonlinear payment remains in the A3 family itself.
      factoredFullIsFourA3SignedSum :
        (cutoff : Nat) (time : Time) →
        Live.factoredFull T R cutoff time
        ≡ R299.four
            * Local.sumSignedRateVectorPayment (familyAt cutoff time)

      cutoffIndependentBound : Time → ℚ

      integratedA3ResidualBudgetsPaid :
        (cutoff : Nat) (terminal : Time) →
        integrateTo
          (λ time →
            R299.four
              * Local.sumResidualBudgets (familyAt cutoff time))
          terminal
        ≤ cutoffIndependentBound terminal

  open A3FactoredFullSameObjectProducer public

  pointwiseFactoredFullUpper :
    ∀ {T R} →
    (P : A3FactoredFullSameObjectProducer T R) →
    (cutoff : Nat) (time : Time) →
    Live.factoredFull T R cutoff time
    ≤
    R299.four
      * Local.sumResidualBudgets (familyAt P cutoff time)
  pointwiseFactoredFullUpper P cutoff time =
    let
      family = familyAt P cutoff time

      localPayment :
        Local.sumSignedRateVectorPayment family
        ≤ Local.sumResidualBudgets family
      localPayment =
        Local.liveA3FamilySumWithoutOutputCardinalityFactor family

      scaled :
        R299.four * Local.sumSignedRateVectorPayment family
        ≤ R299.four * Local.sumResidualBudgets family
      scaled =
        Global.fourTimesMonotone localPayment
    in
    subst
      (λ left →
        left ≤ R299.four * Local.sumResidualBudgets family)
      (sym (factoredFullIsFourA3SignedSum P cutoff time))
      scaled

  integratedFactoredFullUpper :
    ∀ {T R} →
    (P : A3FactoredFullSameObjectProducer T R) →
    (cutoff : Nat) (terminal : Time) →
    integrateTo (Live.factoredFull T R cutoff) terminal
    ≤ cutoffIndependentBound P terminal
  integratedFactoredFullUpper P cutoff terminal =
    ℚP.≤-trans
      (A3.integrateMonotone orderIntegration
        (Live.factoredFull _ _ cutoff)
        (λ time →
          R299.four
            * Local.sumResidualBudgets (familyAt P cutoff time))
        (pointwiseFactoredFullUpper P cutoff)
        terminal)
      (integratedA3ResidualBudgetsPaid P cutoff terminal)

  a3BuildsLiteralFactoredFullBudget :
    ∀ {T R} →
    A3FactoredFullSameObjectProducer T R →
    FactoredBudget.LiteralFactoredFullSpacetimeBudget567 T R
  a3BuildsLiteralFactoredFullBudget P =
    R567.ExactFactoredBudget.literal-factored-full-spacetime-budget-567
      (cutoffIndependentBound P)
      (integratedFactoredFullUpper P)

------------------------------------------------------------------------
-- Frontier / no-collapse status.
------------------------------------------------------------------------

a3ToFactoredFullCompilerClosed : Bool
a3ToFactoredFullCompilerClosed = true

a3ToFactoredFullRequiresNewNonlinearEstimateAfterA3 : Bool
a3ToFactoredFullRequiresNewNonlinearEstimateAfterA3 = false

a3ToFactoredFullExactSameObjectWeldClosed : Bool
a3ToFactoredFullExactSameObjectWeldClosed = false

directA3CovarianceEqualsR406StillRequired : Bool
directA3CovarianceEqualsR406StillRequired = false

weightedFactoredFullIsPreferredConsumerBridge : Bool
weightedFactoredFullIsPreferredConsumerBridge = true

a3ToFactoredFullCompilerClosedIsTrue :
  a3ToFactoredFullCompilerClosed ≡ true
a3ToFactoredFullCompilerClosedIsTrue = refl

a3ToFactoredFullRequiresNewNonlinearEstimateAfterA3IsFalse :
  a3ToFactoredFullRequiresNewNonlinearEstimateAfterA3 ≡ false
a3ToFactoredFullRequiresNewNonlinearEstimateAfterA3IsFalse = refl

a3ToFactoredFullExactSameObjectWeldClosedIsFalse :
  a3ToFactoredFullExactSameObjectWeldClosed ≡ false
a3ToFactoredFullExactSameObjectWeldClosedIsFalse = refl

directA3CovarianceEqualsR406StillRequiredIsFalse :
  directA3CovarianceEqualsR406StillRequired ≡ false
directA3CovarianceEqualsR406StillRequiredIsFalse = refl

weightedFactoredFullIsPreferredConsumerBridgeIsTrue :
  weightedFactoredFullIsPreferredConsumerBridge ≡ true
weightedFactoredFullIsPreferredConsumerBridgeIsTrue = refl
