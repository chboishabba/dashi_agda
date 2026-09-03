module DASHI.Analysis.RiemannG2AdaptiveJLambdaConstantWindowExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ADAPTIVE J*LAMBDA CONSTANT-WINDOW CONSUMER
--
-- The 8894 density return and the earlier quarter-period no-cancellation theorem
-- live on the same inverse-width scale.  Rather than treating either as a
-- scalar-status receipt, this owner makes the surviving compatibility question
-- a typed interval witness on one literal scaled cutoff x = J*Lambda.
--
-- The concrete real-arithmetic producer may later instantiate Scalar, lower and
-- upper with pi/2 and pi/3 + pi^3 A/(6c) + lower-order terms.  This module does
-- not invent that arithmetic; it fixes the exact consumer shape.
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
    false refl
    false refl
    false refl
    "The surviving adaptive gap-split question is a single-object interval problem for x = J*Lambda: the same x must exceed the quarter-period lower constant and remain below the density-derived upper constant. This compatibility is necessary for that route but is not itself an off-ordinate bound, clustering theorem, Gamma repair or RH proof. If the concrete constants leave no interval, prune the gap-split route; if they do, a genuine clustering/signed estimate is still required."
