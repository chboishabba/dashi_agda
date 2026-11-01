module DASHI.Analysis.RiemannG2AdaptiveJLambdaConstantWindowExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotleQuarterPeriodDensityWindowLeanReturnExact as Q37

------------------------------------------------------------------------
-- ADAPTIVE J*LAMBDA CONSTANT-WINDOW CONSUMER
--
-- This is the pre-existing typed same-object consumer.  The later checked §37
-- Lean return now supplies the concrete real-arithmetic producer: it proves the
-- exact density upper endpoint, the leading compatibility criterion, and an
-- actual Nat cutoff in the joint window under its stated hypotheses.
--
-- We therefore keep this generic consumer, but the old statement that its
-- concrete producer is future work is obsolete.  The producer is Lean-owned and
-- not replayed as an Agda real-analysis proof.
------------------------------------------------------------------------

record OrderedWindowCarrier : Set₁ where
  field
    Scalar : Set
    _<_ : Scalar → Scalar → Set

open OrderedWindowCarrier public

record AdaptiveJLambdaWindow
    (C : OrderedWindowCarrier) : Set where
  constructor adaptive-jlambda-window
  field
    scaledCutoff : Scalar C
    quarterPeriodLower : Scalar C
    densityUpper : Scalar C

    crossesQuarterPeriod :
      _<_ C quarterPeriodLower scaledCutoff

    satisfiesDensityCap :
      _<_ C scaledCutoff densityUpper

open AdaptiveJLambdaWindow public

record WindowConstantsCompatible
    (C : OrderedWindowCarrier)
    (lower upper : Scalar C) : Set where
  constructor window-constants-compatible
  field
    witness : Scalar C
    lowerBelowWitness : _<_ C lower witness
    witnessBelowUpper : _<_ C witness upper

open WindowConstantsCompatible public

adaptiveWindowGivesConstantCompatibility :
  ∀ {C} →
  (W : AdaptiveJLambdaWindow C) →
  WindowConstantsCompatible C
    (quarterPeriodLower W)
    (densityUpper W)
adaptiveWindowGivesConstantCompatibility W =
  window-constants-compatible
    (scaledCutoff W)
    (crossesQuarterPeriod W)
    (satisfiesDensityCap W)

------------------------------------------------------------------------
-- BIDI producer weld: concrete arithmetic now exists in checked Lean.
------------------------------------------------------------------------

concreteWindowArithmeticCheckedInLean :
  Q37.machineCheckedInLean Q37.canonicalQuarterPeriodDensityWindowReturn ≡ true
concreteWindowArithmeticCheckedInLean = refl

concreteNatCutoffExistenceCheckedInLean :
  Q37.explicitIntegerCutoffExistenceOwnedInLean
    Q37.canonicalQuarterPeriodDensityWindowReturn ≡ true
concreteNatCutoffExistenceCheckedInLean = refl

concreteWindowArithmeticNotTransportedIntoAgda :
  Q37.transportedIntoAgda Q37.canonicalQuarterPeriodDensityWindowReturn ≡ false
concreteWindowArithmeticNotTransportedIntoAgda = refl

------------------------------------------------------------------------
-- Same-object payment: the lower and upper constraints must concern the same
-- scaled cutoff.  Separate existence statements for two unrelated J*Lambda
-- values are deliberately insufficient.
------------------------------------------------------------------------

record AdaptiveWindowSameObjectBoundary : Set where
  constructor adaptive-window-same-object-boundary
  field
    quarterPeriodAndDensityMayUseDifferentScaledCutoffs : Bool
    quarterPeriodAndDensityMayUseDifferentScaledCutoffsIsFalse :
      quarterPeriodAndDensityMayUseDifferentScaledCutoffs ≡ false

    oneLiteralScaledCutoffRequired : Bool
    oneLiteralScaledCutoffRequiredIsTrue : oneLiteralScaledCutoffRequired ≡ true

    concreteArithmeticProducerNowOwnedInLean : Bool
    concreteArithmeticProducerNowOwnedInLeanIsTrue :
      concreteArithmeticProducerNowOwnedInLean ≡ true

    densityCutAloneRefutesAdaptiveRoute : Bool
    densityCutAloneRefutesAdaptiveRouteIsFalse :
      densityCutAloneRefutesAdaptiveRoute ≡ false

    compatibilityWitnessAloneProvesFinalOffOrdinateBudget : Bool
    compatibilityWitnessAloneProvesFinalOffOrdinateBudgetIsFalse :
      compatibilityWitnessAloneProvesFinalOffOrdinateBudget ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalAdaptiveWindowSameObjectBoundary : AdaptiveWindowSameObjectBoundary
canonicalAdaptiveWindowSameObjectBoundary =
  adaptive-window-same-object-boundary
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "The generic same-object x = J*Lambda consumer is now fed by the checked §37 Lean producer: the real-arithmetic constant comparison and Nat cutoff existence are no longer open search leaves. This closes the window-compatibility payment without promoting Lean proofs into Agda. A compatible cutoff still does not prove the required low-gap clustering, signed finite-near estimate, Gamma repair, or RH."
