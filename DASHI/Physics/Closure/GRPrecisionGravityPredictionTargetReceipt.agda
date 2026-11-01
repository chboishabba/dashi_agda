module DASHI.Physics.Closure.GRPrecisionGravityPredictionTargetReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Candidate256PhysicalCalibrationExternalReceipt
  as Cal
import DASHI.Physics.Closure.DiscreteToSmoothEinsteinLimitReceipt
  as Smooth
import DASHI.Physics.Closure.GRWeakFieldPredictionReceipt as Weak
import DASHI.Physics.Closure.SchwarzschildLimitCandidate as Schwarzschild
import DASHI.Physics.Closure.W4MatterStressEnergyInterfaceReceipt as W4

------------------------------------------------------------------------
-- Precision gravity prediction target.
--
-- This receipt sits above the weak-field GR baseline receipt.  It records the
-- exact missing mathematical surfaces that must be inhabited before DASHI can
-- make an internal carrier-derived Earth/solar-system gravity prediction or a
-- higher-curvature coefficient prediction.
--
-- The current lane is executable only as an external GR baseline plus a
-- diagnostic coefficient budget.  It does not derive Newton's constant,
-- Earth's mass source, Schwarzschild geometry, smooth Einstein convergence, or
-- higher-curvature coefficients from the carrier.

data GRPrecisionGravityPredictionStatus : Set where
  precisionGravityTargetRecorded_failClosed :
    GRPrecisionGravityPredictionStatus

data GRPrecisionGravityObservableTarget : Set where
  recoverMercuryPerihelionBaseline :
    GRPrecisionGravityObservableTarget

  recoverSolarLimbDeflectionBaseline :
    GRPrecisionGravityObservableTarget

  recoverShapiroDelayBaseline :
    GRPrecisionGravityObservableTarget

  recoverEarthSurfaceAcceleration :
    GRPrecisionGravityObservableTarget

  predictHigherCurvatureCoefficientAlpha1 :
    GRPrecisionGravityObservableTarget

  predictHigherCurvatureCoefficientAlpha2 :
    GRPrecisionGravityObservableTarget

canonicalGRPrecisionGravityObservableTargets :
  List GRPrecisionGravityObservableTarget
canonicalGRPrecisionGravityObservableTargets =
  recoverMercuryPerihelionBaseline
  ∷ recoverSolarLimbDeflectionBaseline
  ∷ recoverShapiroDelayBaseline
  ∷ recoverEarthSurfaceAcceleration
  ∷ predictHigherCurvatureCoefficientAlpha1
  ∷ predictHigherCurvatureCoefficientAlpha2
  ∷ []

data GRPrecisionGravityBlocker : Set where
  blockedByCandidate256PhysicalCalibration :
    GRPrecisionGravityBlocker

  blockedByW4MatterStressEnergyInterface :
    GRPrecisionGravityBlocker

  blockedByRadialValuationAndSchwarzschildMatch :
    GRPrecisionGravityBlocker

  blockedByDiscreteToSmoothRicciEinsteinLimit :
    GRPrecisionGravityBlocker

  blockedByCarrierHigherCurvatureCoefficientMap :
    GRPrecisionGravityBlocker

canonicalGRPrecisionGravityBlockers :
  List GRPrecisionGravityBlocker
canonicalGRPrecisionGravityBlockers =
  blockedByCandidate256PhysicalCalibration
  ∷ blockedByW4MatterStressEnergyInterface
  ∷ blockedByRadialValuationAndSchwarzschildMatch
  ∷ blockedByDiscreteToSmoothRicciEinsteinLimit
  ∷ blockedByCarrierHigherCurvatureCoefficientMap
  ∷ []

data GRPrecisionGravityNextLemma : Set where
  constructCandidate256PhysicalCalibrationExternalReceipt :
    GRPrecisionGravityNextLemma

  constructW4MatterStressEnergyInterfaceReceipt :
    GRPrecisionGravityNextLemma

  proveCarrierRadialValuation :
    GRPrecisionGravityNextLemma

  proveWeakFieldNewtonianPotential :
    GRPrecisionGravityNextLemma

  proveSchwarzschildMetricMatch :
    GRPrecisionGravityNextLemma

  proveDiscreteCurvatureToSmoothCurvatureConvergence :
    GRPrecisionGravityNextLemma

  proveDiscreteRicciToSmoothRicciIdentification :
    GRPrecisionGravityNextLemma

  deriveCarrierHigherCurvatureAlphaCoefficients :
    GRPrecisionGravityNextLemma

canonicalGRPrecisionGravityNextLemmas :
  List GRPrecisionGravityNextLemma
canonicalGRPrecisionGravityNextLemmas =
  constructCandidate256PhysicalCalibrationExternalReceipt
  ∷ constructW4MatterStressEnergyInterfaceReceipt
  ∷ proveCarrierRadialValuation
  ∷ proveWeakFieldNewtonianPotential
  ∷ proveSchwarzschildMetricMatch
  ∷ proveDiscreteCurvatureToSmoothCurvatureConvergence
  ∷ proveDiscreteRicciToSmoothRicciIdentification
  ∷ deriveCarrierHigherCurvatureAlphaCoefficients
  ∷ []

data GRPrecisionGravityPromotion : Set where

grPrecisionGravityPromotionImpossibleHere :
  GRPrecisionGravityPromotion →
  ⊥
grPrecisionGravityPromotionImpossibleHere ()

effectiveActionTargetText :
  String
effectiveActionTargetText =
  "Precision target: S_eff = integral sqrt(-g) ((R - 2 Lambda)/(16 pi G) + alpha1 R^2 + alpha2 R_munu R^munu + ...), with alpha_i predicted from carrier data rather than fitted."

earthGravityPredictionBoundaryText :
  String
earthGravityPredictionBoundaryText =
  "Earth gravity requires a physical mass/stress-energy source, radial valuation, weak-field Newtonian potential, Schwarzschild metric match, and discrete-to-smooth Ricci/Einstein convergence before any carrier-derived prediction is legal."

higherCurvatureBudgetScriptText :
  String
higherCurvatureBudgetScriptText =
  "scripts/gr_precision_higher_curvature_budget.py"

higherCurvatureBudgetOutputText :
  String
higherCurvatureBudgetOutputText =
  "scripts/data/outputs/gr_precision_higher_curvature_budget.{json,csv}"

record GRPrecisionGravityPredictionTargetReceipt : Setω where
  field
    status :
      GRPrecisionGravityPredictionStatus

    statusIsCanonical :
      status ≡ precisionGravityTargetRecorded_failClosed

    weakFieldBaselineReceipt :
      Weak.GRWeakFieldPredictionReceipt

    weakFieldBaselineRunnable :
      Weak.predictionDiagnosticRunnable weakFieldBaselineReceipt ≡ true

    weakFieldIsExternalBaseline :
      Weak.externalGRBaselinePrediction weakFieldBaselineReceipt ≡ true

    weakFieldCarrierInternalPredictionStillFalse :
      Weak.carrierInternalPrediction weakFieldBaselineReceipt ≡ false

    weakFieldGravityPredictionStillFalse :
      Weak.gravityPredictionPromoted weakFieldBaselineReceipt ≡ false

    candidate256Preflight :
      Cal.Candidate256PhysicalCalibrationReceiptPreflight

    candidate256StillBlocked :
      Cal.Candidate256PhysicalCalibrationReceiptPreflight.status
        candidate256Preflight
      ≡
      Cal.blockedAwaitingAcceptedDYAuthorityAndW4ZAdequacy

    w4MatterStressEnergyHalt :
      W4.W4MatterStressEnergyInterfaceExternalHalt

    w4MatterStressEnergyNoMatter :
      W4.W4MatterStressEnergyInterfaceExternalHalt.constructsMatterField
        w4MatterStressEnergyHalt
      ≡
      false

    w4MatterStressEnergyNoTensor :
      W4.W4MatterStressEnergyInterfaceExternalHalt.constructsStressEnergyTensor
        w4MatterStressEnergyHalt
      ≡
      false

    w4MatterStressEnergyNoSourcedEinstein :
      W4.W4MatterStressEnergyInterfaceExternalHalt.promotesSourcedEinstein
        w4MatterStressEnergyHalt
      ≡
      false

    schwarzschildLimitCandidate :
      Schwarzschild.SchwarzschildLimitCandidateDiagnostic

    schwarzschildFirstMissingRadialValuation :
      Schwarzschild.SchwarzschildLimitCandidateDiagnostic.firstMissing
        schwarzschildLimitCandidate
      ≡
      Schwarzschild.missingRadialValuation

    schwarzschildNoPromotion :
      Schwarzschild.SchwarzschildLimitCandidateDiagnostic.status
        schwarzschildLimitCandidate
      ≡
      Schwarzschild.requestSurfaceOnlyNoPromotion

    discreteToSmoothEinsteinLimit :
      Smooth.DiscreteToSmoothEinsteinLimitReceipt

    discreteToSmoothFirstMissingCurvature :
      Smooth.DiscreteToSmoothEinsteinLimitReceipt.firstMissing
        discreteToSmoothEinsteinLimit
      ≡
      Smooth.missingDiscreteToSmoothCurvatureConvergence

    discreteToSmoothNoTerminalPromotion :
      Smooth.DiscreteToSmoothEinsteinLimitReceipt.terminalClaimPromoted
        discreteToSmoothEinsteinLimit
      ≡
      false

    observableTargets :
      List GRPrecisionGravityObservableTarget

    observableTargetsAreCanonical :
      observableTargets ≡ canonicalGRPrecisionGravityObservableTargets

    blockers :
      List GRPrecisionGravityBlocker

    blockersAreCanonical :
      blockers ≡ canonicalGRPrecisionGravityBlockers

    nextLemmas :
      List GRPrecisionGravityNextLemma

    nextLemmasAreCanonical :
      nextLemmas ≡ canonicalGRPrecisionGravityNextLemmas

    effectiveActionTarget :
      String

    effectiveActionTargetIsCanonical :
      effectiveActionTarget ≡ effectiveActionTargetText

    earthGravityPredictionBoundary :
      String

    earthGravityPredictionBoundaryIsCanonical :
      earthGravityPredictionBoundary ≡ earthGravityPredictionBoundaryText

    higherCurvatureBudgetScript :
      String

    higherCurvatureBudgetScriptIsCanonical :
      higherCurvatureBudgetScript ≡ higherCurvatureBudgetScriptText

    higherCurvatureBudgetOutput :
      String

    higherCurvatureBudgetOutputIsCanonical :
      higherCurvatureBudgetOutput ≡ higherCurvatureBudgetOutputText

    diagnosticBudgetRunnable :
      Bool

    diagnosticBudgetRunnableIsTrue :
      diagnosticBudgetRunnable ≡ true

    carrierEarthGravityPredictionDerived :
      Bool

    carrierEarthGravityPredictionDerivedIsFalse :
      carrierEarthGravityPredictionDerived ≡ false

    carrierHigherCurvatureCoefficientsDerived :
      Bool

    carrierHigherCurvatureCoefficientsDerivedIsFalse :
      carrierHigherCurvatureCoefficientsDerived ≡ false

    carrierInternalPrediction :
      Bool

    carrierInternalPredictionIsFalse :
      carrierInternalPrediction ≡ false

    precisionGravityPredictionPromoted :
      Bool

    precisionGravityPredictionPromotedIsFalse :
      precisionGravityPredictionPromoted ≡ false

    continuumGRPromoted :
      Bool

    continuumGRPromotedIsFalse :
      continuumGRPromoted ≡ false

    promotions :
      List GRPrecisionGravityPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      GRPrecisionGravityPromotion →
      ⊥

open GRPrecisionGravityPredictionTargetReceipt public

canonicalGRPrecisionGravityPredictionTargetReceipt :
  GRPrecisionGravityPredictionTargetReceipt
canonicalGRPrecisionGravityPredictionTargetReceipt =
  record
    { status =
        precisionGravityTargetRecorded_failClosed
    ; statusIsCanonical =
        refl
    ; weakFieldBaselineReceipt =
        Weak.canonicalGRWeakFieldPredictionReceipt
    ; weakFieldBaselineRunnable =
        refl
    ; weakFieldIsExternalBaseline =
        refl
    ; weakFieldCarrierInternalPredictionStillFalse =
        refl
    ; weakFieldGravityPredictionStillFalse =
        refl
    ; candidate256Preflight =
        Cal.canonicalCandidate256PhysicalCalibrationReceiptPreflight
    ; candidate256StillBlocked =
        refl
    ; w4MatterStressEnergyHalt =
        W4.canonicalW4MatterStressEnergyInterfaceExternalHalt
    ; w4MatterStressEnergyNoMatter =
        refl
    ; w4MatterStressEnergyNoTensor =
        refl
    ; w4MatterStressEnergyNoSourcedEinstein =
        refl
    ; schwarzschildLimitCandidate =
        Schwarzschild.canonicalSchwarzschildLimitCandidateDiagnostic
    ; schwarzschildFirstMissingRadialValuation =
        refl
    ; schwarzschildNoPromotion =
        refl
    ; discreteToSmoothEinsteinLimit =
        Smooth.canonicalDiscreteToSmoothEinsteinLimitReceipt
    ; discreteToSmoothFirstMissingCurvature =
        refl
    ; discreteToSmoothNoTerminalPromotion =
        refl
    ; observableTargets =
        canonicalGRPrecisionGravityObservableTargets
    ; observableTargetsAreCanonical =
        refl
    ; blockers =
        canonicalGRPrecisionGravityBlockers
    ; blockersAreCanonical =
        refl
    ; nextLemmas =
        canonicalGRPrecisionGravityNextLemmas
    ; nextLemmasAreCanonical =
        refl
    ; effectiveActionTarget =
        effectiveActionTargetText
    ; effectiveActionTargetIsCanonical =
        refl
    ; earthGravityPredictionBoundary =
        earthGravityPredictionBoundaryText
    ; earthGravityPredictionBoundaryIsCanonical =
        refl
    ; higherCurvatureBudgetScript =
        higherCurvatureBudgetScriptText
    ; higherCurvatureBudgetScriptIsCanonical =
        refl
    ; higherCurvatureBudgetOutput =
        higherCurvatureBudgetOutputText
    ; higherCurvatureBudgetOutputIsCanonical =
        refl
    ; diagnosticBudgetRunnable =
        true
    ; diagnosticBudgetRunnableIsTrue =
        refl
    ; carrierEarthGravityPredictionDerived =
        false
    ; carrierEarthGravityPredictionDerivedIsFalse =
        refl
    ; carrierHigherCurvatureCoefficientsDerived =
        false
    ; carrierHigherCurvatureCoefficientsDerivedIsFalse =
        refl
    ; carrierInternalPrediction =
        false
    ; carrierInternalPredictionIsFalse =
        refl
    ; precisionGravityPredictionPromoted =
        false
    ; precisionGravityPredictionPromotedIsFalse =
        refl
    ; continuumGRPromoted =
        false
    ; continuumGRPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        grPrecisionGravityPromotionImpossibleHere
    }

grPrecisionGravityTargetNoCarrierPrediction :
  carrierInternalPrediction canonicalGRPrecisionGravityPredictionTargetReceipt
  ≡
  false
grPrecisionGravityTargetNoCarrierPrediction =
  refl

grPrecisionGravityTargetNoHigherCurvatureDerivation :
  carrierHigherCurvatureCoefficientsDerived
    canonicalGRPrecisionGravityPredictionTargetReceipt
  ≡
  false
grPrecisionGravityTargetNoHigherCurvatureDerivation =
  refl

grPrecisionGravityTargetNoPromotion :
  precisionGravityPredictionPromoted
    canonicalGRPrecisionGravityPredictionTargetReceipt
  ≡
  false
grPrecisionGravityTargetNoPromotion =
  refl
