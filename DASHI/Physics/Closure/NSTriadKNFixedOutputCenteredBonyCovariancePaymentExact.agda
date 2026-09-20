module DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredBonyCovariancePaymentExact where

------------------------------------------------------------------------
-- S2b2d1b2 / MINIMAL QUANTITATIVE PRODUCER AFTER CENTERED BONY SPLIT
--
-- The live covariance owner now proves exactly
--
--   C_k = nu [ FL_k + HH_k + CC_k ],
--
-- where each class scalar is the NEGATIVE coherent work of the globally
-- centered input-Laplacian class vector.
--
-- This record is the least-privilege quantitative producer for that exact
-- carrier.  A caller supplies:
--
--   FL_k <= B_FL,
--   HH_k <= B_HH,
--   CC_k <= theta Q_core + B_core,   theta < 1,
--
-- with nonnegative viscosity.  The compiler returns the direct live fixed-
-- output d1b2 bound
--
--   C_k <= nu [ B_FL + B_HH + theta Q_core + B_core ].
--
-- No historical R440 forcing cross, R284 scalar proxy, class-local recentering,
-- absolute value, or fibre-cardinality factor is required.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

record CenteredBonyCovariancePayment : Set where
  constructor centered-bony-covariance-payment
  field
    viscosity : ℚ
    farLowSigned highHighSigned criticalSigned : ℚ

    farLowBudget highHighBudget : ℚ
    coreCompanionMass coreEDBudget theta : ℚ

    viscosityNN : 0ℚ ≤ viscosity
    thetaNN : 0ℚ ≤ theta
    thetaStrictlyBelowOne : theta < 1

    farLowPaid :
      farLowSigned ≤ farLowBudget

    highHighPaid :
      highHighSigned ≤ highHighBudget

    criticalPaid :
      criticalSigned
      ≤ theta * coreCompanionMass + coreEDBudget

open CenteredBonyCovariancePayment public

totalSigned : CenteredBonyCovariancePayment → ℚ
totalSigned P =
  farLowSigned P + (highHighSigned P + criticalSigned P)

totalBudget : CenteredBonyCovariancePayment → ℚ
totalBudget P =
  farLowBudget P
  + ( highHighBudget P
    + (theta P * coreCompanionMass P + coreEDBudget P))

threeRegionSignedBelowBudget :
  (P : CenteredBonyCovariancePayment) →
  totalSigned P ≤ totalBudget P
threeRegionSignedBelowBudget P =
  ℚP.+-mono-≤
    (farLowPaid P)
    (ℚP.+-mono-≤
      (highHighPaid P)
      (criticalPaid P))

viscosityScaledThreeRegionBound :
  (P : CenteredBonyCovariancePayment) →
  viscosity P * totalSigned P
  ≤ viscosity P * totalBudget P
viscosityScaledThreeRegionBound P =
  let instance nuNN = nonNegative (viscosityNN P)
  in
  ℚP.*-monoˡ-≤-nonNeg
    (viscosity P)
    (threeRegionSignedBelowBudget P)

normalizedBudgetShape :
  (P : CenteredBonyCovariancePayment) →
  viscosity P * totalBudget P
  ≡
  viscosity P *
    ( farLowBudget P + highHighBudget P
    + theta P * coreCompanionMass P + coreEDBudget P )
normalizedBudgetShape P =
  solve
    ( viscosity P
    ∷ farLowBudget P
    ∷ highHighBudget P
    ∷ theta P
    ∷ coreCompanionMass P
    ∷ coreEDBudget P
    ∷ [])

centeredBonyCovariancePaymentCompilerClosed : Bool
centeredBonyCovariancePaymentCompilerClosed = true

historicalR440ForcingCrossRequired : Bool
historicalR440ForcingCrossRequired = false

classLocalRecenteringRequired : Bool
classLocalRecenteringRequired = false

absoluteValueRequired : Bool
absoluteValueRequired = false

criticalCoreRelativeCovarianceStillProducerInput : Bool
criticalCoreRelativeCovarianceStillProducerInput = true

clayPromotion : Bool
clayPromotion = false

centeredBonyCovariancePaymentCompilerClosedIsTrue :
  centeredBonyCovariancePaymentCompilerClosed ≡ true
centeredBonyCovariancePaymentCompilerClosedIsTrue = refl
