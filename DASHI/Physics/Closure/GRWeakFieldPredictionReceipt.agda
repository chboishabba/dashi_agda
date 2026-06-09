module DASHI.Physics.Closure.GRWeakFieldPredictionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierDimensionfulPredictionsReceipt as Dim
import DASHI.Physics.Closure.CosmologicalConstantSequesteringReceiptSurface
  as Lambda
import DASHI.Physics.Closure.KnownLimitsGRBridgeTheorem as KnownGR
import DASHI.Physics.Closure.MillenniumTowerGRInstanceReceipt as TowerGR
import DASHI.Physics.Closure.SchwarzschildLimitCandidate as Schwarzschild
import DASHI.Physics.Closure.WaldGRAuthorityReceipt as Wald

------------------------------------------------------------------------
-- Weak-field gravity prediction surface.
--
-- This is the first prediction-capable gravity lane.  It is deliberately
-- fail-closed: the numerical outputs are standard weak-field GR baseline
-- observables, calibrated by external constants and Wald/known-limits GR
-- authority.  They make the lane executable and falsifiable, but they are
-- not carrier-derived DASHI gravity predictions until the finite GR,
-- stress-energy, and discrete-to-smooth blockers are discharged.

data GRWeakFieldPredictionStatus : Set where
  weakFieldBaselinePredictionSurfaceRecorded :
    GRWeakFieldPredictionStatus

data GRWeakFieldObservable : Set where
  mercuryPerihelionAdvance :
    GRWeakFieldObservable

  solarLimbLightDeflection :
    GRWeakFieldObservable

  solarShapiroDelayScale :
    GRWeakFieldObservable

  solarSurfaceGravitationalRedshift :
    GRWeakFieldObservable

canonicalGRWeakFieldObservables :
  List GRWeakFieldObservable
canonicalGRWeakFieldObservables =
  mercuryPerihelionAdvance
  ∷ solarLimbLightDeflection
  ∷ solarShapiroDelayScale
  ∷ solarSurfaceGravitationalRedshift
  ∷ []

data GRWeakFieldPredictionBlocker : Set where
  missingCarrierDerivedNewtonConstant :
    GRWeakFieldPredictionBlocker

  missingCarrierLeviCivitaContinuumBridge :
    GRWeakFieldPredictionBlocker

  missingW4PhysicalStressEnergySource :
    GRWeakFieldPredictionBlocker

  missingDiscreteToSmoothEinsteinLimit :
    GRWeakFieldPredictionBlocker

  missingCarrierDerivedPostNewtonianParameters :
    GRWeakFieldPredictionBlocker

canonicalGRWeakFieldPredictionBlockers :
  List GRWeakFieldPredictionBlocker
canonicalGRWeakFieldPredictionBlockers =
  missingCarrierDerivedNewtonConstant
  ∷ missingCarrierLeviCivitaContinuumBridge
  ∷ missingW4PhysicalStressEnergySource
  ∷ missingDiscreteToSmoothEinsteinLimit
  ∷ missingCarrierDerivedPostNewtonianParameters
  ∷ []

data GRWeakFieldPredictionPromotion : Set where

grWeakFieldPredictionPromotionImpossibleHere :
  GRWeakFieldPredictionPromotion →
  ⊥
grWeakFieldPredictionPromotionImpossibleHere ()

mercuryPredictionText : String
mercuryPredictionText =
  "Mercury perihelion advance baseline: 6*pi*G*M_sun/(a*(1-e^2)*c^2) = about 42.98 arcsec/century."

lightDeflectionPredictionText : String
lightDeflectionPredictionText =
  "Solar-limb light deflection baseline: 4*G*M_sun/(c^2*R_sun) = about 1.750 arcsec."

shapiroPredictionText : String
shapiroPredictionText =
  "Solar Shapiro delay scale baseline: 2*G*M_sun/c^3 = about 9.85 microseconds; full two-way geometry adds the logarithmic path factor."

redshiftPredictionText : String
redshiftPredictionText =
  "Solar surface gravitational redshift baseline: G*M_sun/(R_sun*c^2) = about 2.12e-6, equivalent to about 636 m/s."

diagnosticScriptPathText : String
diagnosticScriptPathText =
  "scripts/run_solar_weak_field_gr_baseline_diagnostic.py"

diagnosticOutputPathText : String
diagnosticOutputPathText =
  "scripts/data/outputs/solar_weak_field_gr_baseline_diagnostic.{json,csv}"

predictionBoundaryText : String
predictionBoundaryText =
  "Prediction-capable means executable weak-field baseline observables.  It does not mean carrier-derived GR: Newton's constant, stress-energy, Levi-Civita continuum bridge, PPN parameters, and the discrete-to-smooth Einstein limit remain externally calibrated or open."

record GRWeakFieldPredictionReceipt : Setω where
  field
    status :
      GRWeakFieldPredictionStatus

    statusIsCanonical :
      status ≡ weakFieldBaselinePredictionSurfaceRecorded

    knownLimitsGRBridge :
      KnownGR.KnownLimitsGRBridgeTheorem

    waldAuthority :
      Wald.WaldGRAuthorityReceipt

    waldBoundaryStillFailClosed :
      Wald.acceptedContinuumAuthorityConstructedHere waldAuthority ≡ false

    towerGRInstance :
      TowerGR.MillenniumTowerGRInstanceReceipt

    towerGRNoPromotion :
      TowerGR.grPromotion towerGRInstance ≡ false

    schwarzschildLimitCandidate :
      Schwarzschild.SchwarzschildLimitCandidateDiagnostic

    schwarzschildFirstMissingRadialValuation :
      Schwarzschild.SchwarzschildLimitCandidateDiagnostic.firstMissing
        schwarzschildLimitCandidate
      ≡
      Schwarzschild.missingRadialValuation

    schwarzschildWeakFieldStillUnsupported :
      Schwarzschild.SchwarzschildLimitCandidateDiagnostic.status
        schwarzschildLimitCandidate
      ≡
      Schwarzschild.requestSurfaceOnlyNoPromotion

    dimensionfulPredictionReceipt :
      Dim.CarrierDimensionfulPredictionsReceipt

    externalAnchorRequired :
      Dim.externalAnchorRequired dimensionfulPredictionReceipt ≡ true

    dimensionfulCarrierPredictionStillOpen :
      Dim.terminalPhysicalPredictionPromoted dimensionfulPredictionReceipt
      ≡
      false

    cosmologicalConstantSurface :
      Lambda.CosmologicalConstantWaldCoefficientDispositionSurface

    cosmologicalConstantCoefficientsNotSelectedHere :
      Lambda.coefficientValuesSelectedHere cosmologicalConstantSurface
      ≡
      false

    observables :
      List GRWeakFieldObservable

    observablesAreCanonical :
      observables ≡ canonicalGRWeakFieldObservables

    mercuryPerihelionAdvanceBaseline :
      String

    mercuryPerihelionAdvanceBaselineIsCanonical :
      mercuryPerihelionAdvanceBaseline ≡ mercuryPredictionText

    solarLimbDeflectionBaseline :
      String

    solarLimbDeflectionBaselineIsCanonical :
      solarLimbDeflectionBaseline ≡ lightDeflectionPredictionText

    solarShapiroDelayScaleBaseline :
      String

    solarShapiroDelayScaleBaselineIsCanonical :
      solarShapiroDelayScaleBaseline ≡ shapiroPredictionText

    solarRedshiftBaseline :
      String

    solarRedshiftBaselineIsCanonical :
      solarRedshiftBaseline ≡ redshiftPredictionText

    carrierInternalPrediction :
      Bool

    carrierInternalPredictionIsFalse :
      carrierInternalPrediction ≡ false

    externalGRBaselinePrediction :
      Bool

    externalGRBaselinePredictionIsTrue :
      externalGRBaselinePrediction ≡ true

    calibrationRequired :
      Bool

    calibrationRequiredIsTrue :
      calibrationRequired ≡ true

    predictionDiagnosticRunnable :
      Bool

    predictionDiagnosticRunnableIsTrue :
      predictionDiagnosticRunnable ≡ true

    diagnosticScriptPath :
      String

    diagnosticScriptPathIsCanonical :
      diagnosticScriptPath ≡ diagnosticScriptPathText

    diagnosticOutputPath :
      String

    diagnosticOutputPathIsCanonical :
      diagnosticOutputPath ≡ diagnosticOutputPathText

    carrierDerivedPostNewtonianParameters :
      Bool

    carrierDerivedPostNewtonianParametersIsFalse :
      carrierDerivedPostNewtonianParameters ≡ false

    sourcedEinsteinEquationPromoted :
      Bool

    sourcedEinsteinEquationPromotedIsFalse :
      sourcedEinsteinEquationPromoted ≡ false

    continuumGRPromoted :
      Bool

    continuumGRPromotedIsFalse :
      continuumGRPromoted ≡ false

    gravityPredictionPromoted :
      Bool

    gravityPredictionPromotedIsFalse :
      gravityPredictionPromoted ≡ false

    blockers :
      List GRWeakFieldPredictionBlocker

    blockersAreCanonical :
      blockers ≡ canonicalGRWeakFieldPredictionBlockers

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ predictionBoundaryText

    promotions :
      List GRWeakFieldPredictionPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      GRWeakFieldPredictionPromotion →
      ⊥

open GRWeakFieldPredictionReceipt public

canonicalGRWeakFieldPredictionReceipt :
  GRWeakFieldPredictionReceipt
canonicalGRWeakFieldPredictionReceipt =
  record
    { status =
        weakFieldBaselinePredictionSurfaceRecorded
    ; statusIsCanonical =
        refl
    ; knownLimitsGRBridge =
        KnownGR.canonicalKnownLimitsGRBridgeTheorem
    ; waldAuthority =
        Wald.canonicalWaldGRAuthorityReceipt
    ; waldBoundaryStillFailClosed =
        refl
    ; towerGRInstance =
        TowerGR.canonicalMillenniumTowerGRInstanceReceipt
    ; towerGRNoPromotion =
        refl
    ; schwarzschildLimitCandidate =
        Schwarzschild.canonicalSchwarzschildLimitCandidateDiagnostic
    ; schwarzschildFirstMissingRadialValuation =
        refl
    ; schwarzschildWeakFieldStillUnsupported =
        refl
    ; dimensionfulPredictionReceipt =
        Dim.canonicalCarrierDimensionfulPredictionsReceipt
    ; externalAnchorRequired =
        refl
    ; dimensionfulCarrierPredictionStillOpen =
        refl
    ; cosmologicalConstantSurface =
        Lambda.canonicalCosmologicalConstantWaldCoefficientDispositionSurface
    ; cosmologicalConstantCoefficientsNotSelectedHere =
        refl
    ; observables =
        canonicalGRWeakFieldObservables
    ; observablesAreCanonical =
        refl
    ; mercuryPerihelionAdvanceBaseline =
        mercuryPredictionText
    ; mercuryPerihelionAdvanceBaselineIsCanonical =
        refl
    ; solarLimbDeflectionBaseline =
        lightDeflectionPredictionText
    ; solarLimbDeflectionBaselineIsCanonical =
        refl
    ; solarShapiroDelayScaleBaseline =
        shapiroPredictionText
    ; solarShapiroDelayScaleBaselineIsCanonical =
        refl
    ; solarRedshiftBaseline =
        redshiftPredictionText
    ; solarRedshiftBaselineIsCanonical =
        refl
    ; carrierInternalPrediction =
        false
    ; carrierInternalPredictionIsFalse =
        refl
    ; externalGRBaselinePrediction =
        true
    ; externalGRBaselinePredictionIsTrue =
        refl
    ; calibrationRequired =
        true
    ; calibrationRequiredIsTrue =
        refl
    ; predictionDiagnosticRunnable =
        true
    ; predictionDiagnosticRunnableIsTrue =
        refl
    ; diagnosticScriptPath =
        diagnosticScriptPathText
    ; diagnosticScriptPathIsCanonical =
        refl
    ; diagnosticOutputPath =
        diagnosticOutputPathText
    ; diagnosticOutputPathIsCanonical =
        refl
    ; carrierDerivedPostNewtonianParameters =
        false
    ; carrierDerivedPostNewtonianParametersIsFalse =
        refl
    ; sourcedEinsteinEquationPromoted =
        false
    ; sourcedEinsteinEquationPromotedIsFalse =
        refl
    ; continuumGRPromoted =
        false
    ; continuumGRPromotedIsFalse =
        refl
    ; gravityPredictionPromoted =
        false
    ; gravityPredictionPromotedIsFalse =
        refl
    ; blockers =
        canonicalGRWeakFieldPredictionBlockers
    ; blockersAreCanonical =
        refl
    ; boundary =
        predictionBoundaryText
    ; boundaryIsCanonical =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        grWeakFieldPredictionPromotionImpossibleHere
    }

canonicalGRWeakFieldPredictionRunnable :
  predictionDiagnosticRunnable canonicalGRWeakFieldPredictionReceipt ≡ true
canonicalGRWeakFieldPredictionRunnable =
  refl

canonicalGRWeakFieldNoPromotion :
  gravityPredictionPromoted canonicalGRWeakFieldPredictionReceipt ≡ false
canonicalGRWeakFieldNoPromotion =
  refl
