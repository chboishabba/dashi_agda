module DASHI.Foundations.SurrealCompactificationTailBoundBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Foundations.SurrealCompactification as SC
import DASHI.Foundations.SurrealCompactificationIntake as Intake
import DASHI.Foundations.SurrealCompactificationRationalBridge as RationalBridge

------------------------------------------------------------------------
-- Exact fail-closed analytic law shapes.
--
-- These records expose the compactification/tail-bound bridge requested by
-- downstream modules.  They connect only checked finite towers, symbolic
-- rational approximants, and the intake authority records.  The analytic
-- geometric-series and kappa inequalities remain fail-closed authority slots.

record GeometricSeriesTailLawShape (n : Nat) : Set₁ where
  constructor geometric-series-tail
  field
    tailStart :
      Nat

    tailStartIsN :
      tailStart ≡ n

    tailFormula :
      String

    tailFormulaIsCanonical :
      tailFormula ≡ "sum_{i>=n} 3^-i"

    tailGauge :
      Intake.SymbolicGauge

    tailGaugeIsThreeMinusN :
      tailGauge ≡ Intake.threeToMinus n

    tailBoundIntake :
      Intake.TailBoundIntake n

    tailBoundIntakeIsCanonical :
      tailBoundIntake ≡ Intake.canonicalTailBoundIntake n

    finiteTowerCarrier :
      Nat →
      Set

    finiteTowerCarrierIsInternal :
      finiteTowerCarrier ≡ SC.FiniteTritTower

    symbolicRationalCarrier :
      Set

    symbolicRationalCarrierIsInternal :
      symbolicRationalCarrier
      ≡
      RationalBridge.SymbolicRationalApproximation

    rationalBridge :
      RationalBridge.FiniteTritTowerSymbolicRationalBridge

    rationalBridgeIsCanonical :
      rationalBridge
      ≡
      RationalBridge.canonicalFiniteTritTowerSymbolicRationalBridge

    analyticProofStatus :
      Intake.IntakeCheckStatus

    analyticProofStatusIsFailClosed :
      analyticProofStatus ≡ Intake.externalAuthorityRequiredFailClosed

    analyticTailBoundProvedHere :
      Bool

    analyticTailBoundProvedHereIsFalse :
      analyticTailBoundProvedHere ≡ false

    analyticTailBoundPromoted :
      Bool

    analyticTailBoundPromotedIsFalse :
      analyticTailBoundPromoted ≡ false

open GeometricSeriesTailLawShape public

geometric-series-tail-law :
  (n : Nat) →
  GeometricSeriesTailLawShape n
geometric-series-tail-law n =
  geometric-series-tail
    n
    refl
    "sum_{i>=n} 3^-i"
    refl
    (Intake.threeToMinus n)
    refl
    (Intake.canonicalTailBoundIntake n)
    refl
    SC.FiniteTritTower
    refl
    RationalBridge.SymbolicRationalApproximation
    refl
    RationalBridge.canonicalFiniteTritTowerSymbolicRationalBridge
    refl
    Intake.externalAuthorityRequiredFailClosed
    refl
    false
    refl
    false
    refl

record KappaTailBoundLawShape (n k : Nat) : Set₁ where
  constructor kappaTailBound
  field
    geometricTail :
      GeometricSeriesTailLawShape n

    geometricTailIsCanonical :
      geometricTail ≡ geometric-series-tail-law n

    truncationKappaIntake :
      Intake.TruncationKappaIntake k

    truncationKappaIntakeIsCanonical :
      truncationKappaIntake ≡ Intake.canonicalTruncationKappaIntake k

    kappaReference :
      Intake.KappaShape

    kappaReferenceIsAtK :
      kappaReference ≡ Intake.kappaOfDepth k

    exactCheckedRationalBridgeFields :
      Intake.ExactCheckedRationalBridgeFields n n k

    exactCheckedRationalBridgeFieldsAreCanonical :
      exactCheckedRationalBridgeFields
      ≡
      Intake.canonicalExactCheckedRationalBridgeFields n n k

    internalTruncationSurface :
      SC.InternalBoundedTruncationSurface

    internalTruncationSurfaceIsCanonical :
      internalTruncationSurface
      ≡
      SC.canonicalInternalBoundedTruncationSurface

    compactificationIntake :
      Intake.SurrealCompactificationIntakeContract

    compactificationIntakeIsCanonical :
      compactificationIntake
      ≡
      Intake.canonicalSurrealCompactificationIntakeContract

    noPromotionFlags :
      Intake.NoPromotionFlags

    noPromotionFlagsAreCanonical :
      noPromotionFlags ≡ Intake.canonicalNoPromotionFlags

    kappaAnalyticProofStatus :
      Intake.IntakeCheckStatus

    kappaAnalyticProofStatusIsFailClosed :
      kappaAnalyticProofStatus
      ≡
      Intake.externalAuthorityRequiredFailClosed

    kappaTailBoundProvedHere :
      Bool

    kappaTailBoundProvedHereIsFalse :
      kappaTailBoundProvedHere ≡ false

    kappaTailBoundPromoted :
      Bool

    kappaTailBoundPromotedIsFalse :
      kappaTailBoundPromoted ≡ false

open KappaTailBoundLawShape public

kappaTailBound-law :
  (n k : Nat) →
  KappaTailBoundLawShape n k
kappaTailBound-law n k =
  kappaTailBound
    (geometric-series-tail-law n)
    refl
    (Intake.canonicalTruncationKappaIntake k)
    refl
    (Intake.kappaOfDepth k)
    refl
    (Intake.canonicalExactCheckedRationalBridgeFields n n k)
    refl
    SC.canonicalInternalBoundedTruncationSurface
    refl
    Intake.canonicalSurrealCompactificationIntakeContract
    refl
    Intake.canonicalNoPromotionFlags
    refl
    Intake.externalAuthorityRequiredFailClosed
    refl
    false
    refl
    false
    refl

record CompactificationTailBoundBridgeSurface (n k : Nat) : Set₁ where
  field
    geometricSeriesTail :
      GeometricSeriesTailLawShape n

    geometricSeriesTailIsCanonical :
      geometricSeriesTail ≡ geometric-series-tail-law n

    kappaTailBoundSurface :
      KappaTailBoundLawShape n k

    kappaTailBoundSurfaceIsCanonical :
      kappaTailBoundSurface ≡ kappaTailBound-law n k

    rationalBridge :
      RationalBridge.FiniteTritTowerSymbolicRationalBridge

    rationalBridgeIsCanonical :
      rationalBridge
      ≡
      RationalBridge.canonicalFiniteTritTowerSymbolicRationalBridge

    compactificationSurface :
      SC.InternalBoundedTruncationSurface

    compactificationSurfaceIsCanonical :
      compactificationSurface
      ≡
      SC.canonicalInternalBoundedTruncationSurface

    intakeContract :
      Intake.SurrealCompactificationIntakeContract

    intakeContractIsCanonical :
      intakeContract
      ≡
      Intake.canonicalSurrealCompactificationIntakeContract

    allAnalyticProofsFailClosed :
      Bool

    allAnalyticProofsFailClosedIsTrue :
      allAnalyticProofsFailClosed ≡ true

    anyAnalyticProofPromotedHere :
      Bool

    anyAnalyticProofPromotedHereIsFalse :
      anyAnalyticProofPromotedHere ≡ false

open CompactificationTailBoundBridgeSurface public

canonicalCompactificationTailBoundBridgeSurface :
  (n k : Nat) →
  CompactificationTailBoundBridgeSurface n k
canonicalCompactificationTailBoundBridgeSurface n k =
  record
    { geometricSeriesTail =
        geometric-series-tail-law n
    ; geometricSeriesTailIsCanonical =
        refl
    ; kappaTailBoundSurface =
        kappaTailBound-law n k
    ; kappaTailBoundSurfaceIsCanonical =
        refl
    ; rationalBridge =
        RationalBridge.canonicalFiniteTritTowerSymbolicRationalBridge
    ; rationalBridgeIsCanonical =
        refl
    ; compactificationSurface =
        SC.canonicalInternalBoundedTruncationSurface
    ; compactificationSurfaceIsCanonical =
        refl
    ; intakeContract =
        Intake.canonicalSurrealCompactificationIntakeContract
    ; intakeContractIsCanonical =
        refl
    ; allAnalyticProofsFailClosed =
        true
    ; allAnalyticProofsFailClosedIsTrue =
        refl
    ; anyAnalyticProofPromotedHere =
        false
    ; anyAnalyticProofPromotedHereIsFalse =
        refl
    }

canonicalGeometricSeriesTailFailsClosed :
  (n : Nat) →
  analyticProofStatus (geometric-series-tail-law n)
  ≡
  Intake.externalAuthorityRequiredFailClosed
canonicalGeometricSeriesTailFailsClosed n =
  refl

canonicalKappaTailBoundFailsClosed :
  (n k : Nat) →
  kappaAnalyticProofStatus (kappaTailBound-law n k)
  ≡
  Intake.externalAuthorityRequiredFailClosed
canonicalKappaTailBoundFailsClosed n k =
  refl

canonicalKappaTailBoundDoesNotPromote :
  (n k : Nat) →
  kappaTailBoundPromoted (kappaTailBound-law n k) ≡ false
canonicalKappaTailBoundDoesNotPromote n k =
  refl
