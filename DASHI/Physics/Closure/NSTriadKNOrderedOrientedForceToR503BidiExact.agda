module DASHI.Physics.Closure.NSTriadKNOrderedOrientedForceToR503BidiExact where

------------------------------------------------------------------------
-- ORDERED ORIENTED SIGNED FORCE BUDGET -> R503
--
-- The direct integrated bridge proves on the literal R406 trajectory
--
--   4 * integratedDirectCompanion
--     = 2 * integratedOrderedOrientedForce.
--
-- Therefore the weakest concrete analytic producer may be stated directly on
-- the single signed ordered kernel
--
--   H(alpha,beta) = w(alpha,beta) Re<G_alpha,D_beta>.
--
-- A cutoff-uniform upper bound for 2 * integral H transports definitionally to
-- R503's DirectOffDiagonalBudget.  This file introduces no estimate itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNDirectResolventSignedCrossToR415Round503Exact as R503
import DASHI.Physics.Closure.NSTriadKNDirectIntegratedOrderedOrientedForceBidiExact as Ordered

F : C3.RealField _
F = Rational.rationalRealField

module OrderedToR503
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (integration : R495.IntegrationTransportAuthority Time integrateTo) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Kernel = Ordered.IntegratedOrdered
    Time initialTime integrateTo DerivativeOf integration
  module Direct = R503.DirectSignedCross
    Time initialTime integrateTo DerivativeOf integration

  record OrderedOrientedSpacetimeBudget
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      cutoffIndependentBound : Time → ℚ
      orderedOrientedBudget :
        (cutoff : Nat) (terminal : Time) →
        Ordered.two * Kernel.integratedOrderedOrientedForce T R cutoff terminal
        ≤ cutoffIndependentBound terminal

  open OrderedOrientedSpacetimeBudget public

  orderedBudgetBuildsR503 :
    ∀ {T R} →
    OrderedOrientedSpacetimeBudget T R →
    Direct.DirectOffDiagonalBudget T R
  orderedBudgetBuildsR503 {T} {R} P = record
    { Direct.cutoffIndependentBound = cutoffIndependentBound P
    ; Direct.directOffDiagonalBudget = λ cutoff terminal →
        subst
          (λ lower → lower ≤ cutoffIndependentBound P terminal)
          (sym (Kernel.fourIntegratedDirectIsTwoOrdered T R cutoff terminal))
          (orderedOrientedBudget P cutoff terminal)
    }

------------------------------------------------------------------------
-- Status / exact current min-cut.
------------------------------------------------------------------------

orderedOrientedKernelIsDirectR503Producer : Bool
orderedOrientedKernelIsDirectR503Producer = true

r492ExternalCompanionReceiptRequiredForThisRoute : Bool
r492ExternalCompanionReceiptRequiredForThisRoute = false

independentAmplitudeBudgetRequired : Bool
independentAmplitudeBudgetRequired = false

forcingNormSquareRequired : Bool
forcingNormSquareRequired = false

absoluteValueRequiredBeforeTerminalBudget : Bool
absoluteValueRequiredBeforeTerminalBudget = false

onlyAnalyticFieldIsCutoffUniformSignedOrderedBudget : Bool
onlyAnalyticFieldIsCutoffUniformSignedOrderedBudget = true

cutoffUniformSignedOrderedBudgetClosed : Bool
cutoffUniformSignedOrderedBudgetClosed = false

clayPromotion : Bool
clayPromotion = false

orderedOrientedKernelIsDirectR503ProducerIsTrue :
  orderedOrientedKernelIsDirectR503Producer ≡ true
orderedOrientedKernelIsDirectR503ProducerIsTrue = refl

onlyAnalyticFieldIsCutoffUniformSignedOrderedBudgetIsTrue :
  onlyAnalyticFieldIsCutoffUniformSignedOrderedBudget ≡ true
onlyAnalyticFieldIsCutoffUniformSignedOrderedBudgetIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
