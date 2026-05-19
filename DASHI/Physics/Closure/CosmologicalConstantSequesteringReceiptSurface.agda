module DASHI.Physics.Closure.CosmologicalConstantSequesteringReceiptSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Cosmological-constant sequestering receipt surface.
--
-- This module records the Kaloper-Padilla sequestering v2 strategy as an
-- external-input receipt interface.  It does not derive the cosmological
-- constant from a DASHI carrier, solve the global constraints, construct
-- sigma, prove shift-symmetry protection, calibrate Newton's constant, or
-- establish an observational Lambda bound internally.

data CosmologicalConstantSurfaceStatus : Set where
  cosmologicalConstantInputsOnlyNoCarrierDerivation :
    CosmologicalConstantSurfaceStatus

data CosmologicalConstantPromotionAuthorityToken : Set where

data CompactUniverseInputToken : Set where

data KaloperPadillaSequesteringV2StrategyToken : Set where

data SigmaShiftSymmetryProtectionToken : Set where

data C2NewtonCalibrationReceiptToken : Set where

data C3ObservationalBoundReceiptToken : Set where

data C1SequesteringCancellationReceiptToken : Set where

data ExternalTheoremProvenanceReceiptToken : Set where

data KaloperPadillaV2StrategyComponent : Set where
  compactUniverseGlobalVolumeInput :
    KaloperPadillaV2StrategyComponent

  globalLambdaAndScalingVariables :
    KaloperPadillaV2StrategyComponent

  sigmaProtectedByShiftSymmetry :
    KaloperPadillaV2StrategyComponent

  fourFormOrGlobalConstraintSector :
    KaloperPadillaV2StrategyComponent

  spacetimeAverageTraceConstraint :
    KaloperPadillaV2StrategyComponent

  radiativelyStableVacuumEnergyCancellation :
    KaloperPadillaV2StrategyComponent

canonicalKaloperPadillaV2StrategyComponents :
  List KaloperPadillaV2StrategyComponent
canonicalKaloperPadillaV2StrategyComponents =
  compactUniverseGlobalVolumeInput
  ∷ globalLambdaAndScalingVariables
  ∷ sigmaProtectedByShiftSymmetry
  ∷ fourFormOrGlobalConstraintSector
  ∷ spacetimeAverageTraceConstraint
  ∷ radiativelyStableVacuumEnergyCancellation
  ∷ []

data CosmologicalConstantOpenInput : Set where
  missingCompactUniverseInput :
    CosmologicalConstantOpenInput

  missingKaloperPadillaSequesteringV2StrategyReceipt :
    CosmologicalConstantOpenInput

  missingSigmaShiftSymmetryProtectionReceipt :
    CosmologicalConstantOpenInput

  missingC2NewtonCalibrationReceipt :
    CosmologicalConstantOpenInput

  missingC3ObservationalBoundReceipt :
    CosmologicalConstantOpenInput

  missingC1SequesteringCancellationReceipt :
    CosmologicalConstantOpenInput

  missingExternalTheoremProvenanceReceipt :
    CosmologicalConstantOpenInput

  missingWaldAdapterBinding :
    CosmologicalConstantOpenInput

canonicalCosmologicalConstantOpenInputs :
  List CosmologicalConstantOpenInput
canonicalCosmologicalConstantOpenInputs =
  missingCompactUniverseInput
  ∷ missingKaloperPadillaSequesteringV2StrategyReceipt
  ∷ missingSigmaShiftSymmetryProtectionReceipt
  ∷ missingC2NewtonCalibrationReceipt
  ∷ missingC3ObservationalBoundReceipt
  ∷ missingC1SequesteringCancellationReceipt
  ∷ missingExternalTheoremProvenanceReceipt
  ∷ missingWaldAdapterBinding
  ∷ []

data CosmologicalConstantWaldCoefficientDisposition : Set where
  c1CancelledBySequestering :
    CosmologicalConstantWaldCoefficientDisposition

  c2FixedByNewtonCalibration :
    CosmologicalConstantWaldCoefficientDisposition

  c3ConstrainedByObservation :
    CosmologicalConstantWaldCoefficientDisposition

  c3SelectedZeroWithinCassiniBound :
    CosmologicalConstantWaldCoefficientDisposition

data WaldCoefficientSelectionReceiptStatus : Set where
  waldCoefficientsSelectedModuloExplicitInputs :
    WaldCoefficientSelectionReceiptStatus

data WaldSelectedCoefficient : Set where
  selectedC1SequesteringCancellation :
    WaldSelectedCoefficient

  selectedC2NewtonObservedCalibration :
    WaldSelectedCoefficient

  selectedC3ZeroWithinCassiniBound :
    WaldSelectedCoefficient

canonicalWaldSelectedCoefficients :
  List WaldSelectedCoefficient
canonicalWaldSelectedCoefficients =
  selectedC1SequesteringCancellation
  ∷ selectedC2NewtonObservedCalibration
  ∷ selectedC3ZeroWithinCassiniBound
  ∷ []

record NewtonCalibrationReceipt : Setω where
  field
    calibrationToken :
      C2NewtonCalibrationReceiptToken

    coefficientSelected :
      WaldSelectedCoefficient

    coefficientSelectedIsNewtonCalibration :
      coefficientSelected ≡ selectedC2NewtonObservedCalibration

    calibrationShape :
      String

    calibrationShape-v :
      calibrationShape
      ≡
      "c2-is-fixed-by-the-observed-Newton-constant-normalisation"

    receiptComplete :
      Bool

    receiptCompleteIsTrue :
      receiptComplete ≡ true

    receiptBoundary :
      List String

open NewtonCalibrationReceipt public

record CassiniReceipt : Setω where
  field
    observationalBoundToken :
      C3ObservationalBoundReceiptToken

    coefficientSelected :
      WaldSelectedCoefficient

    coefficientSelectedIsZeroWithinBound :
      coefficientSelected ≡ selectedC3ZeroWithinCassiniBound

    boundShape :
      String

    boundShape-v :
      boundShape
      ≡
      "Cassini-PPN-gamma-bound-permits-selecting-c3-zero-as-the-calibrated-observational-choice"

    receiptComplete :
      Bool

    receiptCompleteIsTrue :
      receiptComplete ≡ true

    receiptBoundary :
      List String

open CassiniReceipt public

newtonCalibrationReceiptFromToken :
  C2NewtonCalibrationReceiptToken →
  NewtonCalibrationReceipt
newtonCalibrationReceiptFromToken token =
  record
    { calibrationToken =
        token
    ; coefficientSelected =
        selectedC2NewtonObservedCalibration
    ; coefficientSelectedIsNewtonCalibration =
        refl
    ; calibrationShape =
        "c2-is-fixed-by-the-observed-Newton-constant-normalisation"
    ; calibrationShape-v =
        refl
    ; receiptComplete =
        true
    ; receiptCompleteIsTrue =
        refl
    ; receiptBoundary =
        "c2 is not derived from the carrier; it is calibrated by the observed Newton constant"
        ∷ "the selected coefficient is the Einstein-Hilbert/Wald ambiguity normalisation compatible with G_N observed"
        ∷ []
    }

cassiniReceiptFromToken :
  C3ObservationalBoundReceiptToken →
  CassiniReceipt
cassiniReceiptFromToken token =
  record
    { observationalBoundToken =
        token
    ; coefficientSelected =
        selectedC3ZeroWithinCassiniBound
    ; coefficientSelectedIsZeroWithinBound =
        refl
    ; boundShape =
        "Cassini-PPN-gamma-bound-permits-selecting-c3-zero-as-the-calibrated-observational-choice"
    ; boundShape-v =
        refl
    ; receiptComplete =
        true
    ; receiptCompleteIsTrue =
        refl
    ; receiptBoundary =
        "c3 is selected as zero within the observational Cassini/PPN bound"
        ∷ "the receipt records an observational calibration, not a carrier theorem that c3 must vanish"
        ∷ []
    }

record CosmologicalConstantWaldCoefficientDispositionSurface : Setω where
  field
    status :
      CosmologicalConstantSurfaceStatus

    c1Disposition :
      CosmologicalConstantWaldCoefficientDisposition

    c1DispositionIsSequesteringCancellation :
      c1Disposition ≡ c1CancelledBySequestering

    c2Disposition :
      CosmologicalConstantWaldCoefficientDisposition

    c2DispositionIsNewtonCalibration :
      c2Disposition ≡ c2FixedByNewtonCalibration

    c3Disposition :
      CosmologicalConstantWaldCoefficientDisposition

    c3DispositionIsObservationalBound :
      c3Disposition ≡ c3ConstrainedByObservation

    coefficientValuesSelectedHere :
      Bool

    coefficientValuesSelectedHereIsFalse :
      coefficientValuesSelectedHere ≡ false

    dispositionBoundary :
      List String

open CosmologicalConstantWaldCoefficientDispositionSurface public

canonicalCosmologicalConstantWaldCoefficientDispositionSurface :
  CosmologicalConstantWaldCoefficientDispositionSurface
canonicalCosmologicalConstantWaldCoefficientDispositionSurface =
  record
    { status =
        cosmologicalConstantInputsOnlyNoCarrierDerivation
    ; c1Disposition =
        c1CancelledBySequestering
    ; c1DispositionIsSequesteringCancellation =
        refl
    ; c2Disposition =
        c2FixedByNewtonCalibration
    ; c2DispositionIsNewtonCalibration =
        refl
    ; c3Disposition =
        c3ConstrainedByObservation
    ; c3DispositionIsObservationalBound =
        refl
    ; coefficientValuesSelectedHere =
        false
    ; coefficientValuesSelectedHereIsFalse =
        refl
    ; dispositionBoundary =
        "c1 is not fit as a free cosmological-constant counterterm here; it is cancelled only by an explicit sequestering receipt"
        ∷ "c2 is fixed only by an explicit Newton-calibration receipt"
        ∷ "c3 is constrained only by an explicit observational-bound receipt"
        ∷ []
    }

record CosmologicalConstantExplicitInputPack : Set where
  field
    compactUniverseInput :
      CompactUniverseInputToken

    sequesteringV2Strategy :
      KaloperPadillaSequesteringV2StrategyToken

    sigmaShiftSymmetryProtection :
      SigmaShiftSymmetryProtectionToken

    c2NewtonCalibration :
      C2NewtonCalibrationReceiptToken

    c3ObservationalBound :
      C3ObservationalBoundReceiptToken

    c1SequesteringCancellation :
      C1SequesteringCancellationReceiptToken

    externalTheoremProvenance :
      ExternalTheoremProvenanceReceiptToken

    inputBoundary :
      List String

open CosmologicalConstantExplicitInputPack public

record CosmologicalConstantReceipt
  (inputs : CosmologicalConstantExplicitInputPack) : Setω where
  constructor cosmologicalConstantReceiptModuloExplicitInputs
  field
    status :
      CosmologicalConstantSurfaceStatus

    explicitInputPack :
      CosmologicalConstantExplicitInputPack

    explicitInputPackIsInputs :
      explicitInputPack ≡ inputs

    coefficientDisposition :
      CosmologicalConstantWaldCoefficientDispositionSurface

    strategyComponents :
      List KaloperPadillaV2StrategyComponent

    strategyComponentsAreCanonical :
      strategyComponents
      ≡
      canonicalKaloperPadillaV2StrategyComponents

    compactUniverseToken :
      CompactUniverseInputToken

    compactUniverseTokenFromInputs :
      compactUniverseToken
      ≡
      CosmologicalConstantExplicitInputPack.compactUniverseInput inputs

    sequesteringV2StrategyToken :
      KaloperPadillaSequesteringV2StrategyToken

    sequesteringV2StrategyTokenFromInputs :
      sequesteringV2StrategyToken
      ≡
      CosmologicalConstantExplicitInputPack.sequesteringV2Strategy inputs

    sigmaProtectionToken :
      SigmaShiftSymmetryProtectionToken

    sigmaProtectionTokenFromInputs :
      sigmaProtectionToken
      ≡
      CosmologicalConstantExplicitInputPack.sigmaShiftSymmetryProtection
        inputs

    c1CancellationToken :
      C1SequesteringCancellationReceiptToken

    c1CancellationTokenFromInputs :
      c1CancellationToken
      ≡
      CosmologicalConstantExplicitInputPack.c1SequesteringCancellation
        inputs

    c2CalibrationToken :
      C2NewtonCalibrationReceiptToken

    c2CalibrationTokenFromInputs :
      c2CalibrationToken
      ≡
      CosmologicalConstantExplicitInputPack.c2NewtonCalibration inputs

    c3BoundToken :
      C3ObservationalBoundReceiptToken

    c3BoundTokenFromInputs :
      c3BoundToken
      ≡
      CosmologicalConstantExplicitInputPack.c3ObservationalBound inputs

    provenanceToken :
      ExternalTheoremProvenanceReceiptToken

    provenanceTokenFromInputs :
      provenanceToken
      ≡
      CosmologicalConstantExplicitInputPack.externalTheoremProvenance
        inputs

    c1Cancelled :
      Bool

    c1CancelledIsTrue :
      c1Cancelled ≡ true

    c2NewtonCalibrated :
      Bool

    c2NewtonCalibratedIsTrue :
      c2NewtonCalibrated ≡ true

    c3ObservationallyBounded :
      Bool

    c3ObservationallyBoundedIsTrue :
      c3ObservationallyBounded ≡ true

    carrierDerivationClaimed :
      Bool

    carrierDerivationClaimedIsFalse :
      carrierDerivationClaimed ≡ false

    receiptBoundary :
      List String

open CosmologicalConstantReceipt public

cosmologicalConstantReceiptFromExplicitInputs :
  (inputs : CosmologicalConstantExplicitInputPack) →
  CosmologicalConstantReceipt inputs
cosmologicalConstantReceiptFromExplicitInputs inputs =
  record
    { status =
        cosmologicalConstantInputsOnlyNoCarrierDerivation
    ; explicitInputPack =
        inputs
    ; explicitInputPackIsInputs =
        refl
    ; coefficientDisposition =
        canonicalCosmologicalConstantWaldCoefficientDispositionSurface
    ; strategyComponents =
        canonicalKaloperPadillaV2StrategyComponents
    ; strategyComponentsAreCanonical =
        refl
    ; compactUniverseToken =
        CosmologicalConstantExplicitInputPack.compactUniverseInput inputs
    ; compactUniverseTokenFromInputs =
        refl
    ; sequesteringV2StrategyToken =
        CosmologicalConstantExplicitInputPack.sequesteringV2Strategy inputs
    ; sequesteringV2StrategyTokenFromInputs =
        refl
    ; sigmaProtectionToken =
        CosmologicalConstantExplicitInputPack.sigmaShiftSymmetryProtection
          inputs
    ; sigmaProtectionTokenFromInputs =
        refl
    ; c1CancellationToken =
        CosmologicalConstantExplicitInputPack.c1SequesteringCancellation
          inputs
    ; c1CancellationTokenFromInputs =
        refl
    ; c2CalibrationToken =
        CosmologicalConstantExplicitInputPack.c2NewtonCalibration inputs
    ; c2CalibrationTokenFromInputs =
        refl
    ; c3BoundToken =
        CosmologicalConstantExplicitInputPack.c3ObservationalBound inputs
    ; c3BoundTokenFromInputs =
        refl
    ; provenanceToken =
        CosmologicalConstantExplicitInputPack.externalTheoremProvenance
          inputs
    ; provenanceTokenFromInputs =
        refl
    ; c1Cancelled =
        true
    ; c1CancelledIsTrue =
        refl
    ; c2NewtonCalibrated =
        true
    ; c2NewtonCalibratedIsTrue =
        refl
    ; c3ObservationallyBounded =
        true
    ; c3ObservationallyBoundedIsTrue =
        refl
    ; carrierDerivationClaimed =
        false
    ; carrierDerivationClaimedIsFalse =
        refl
    ; receiptBoundary =
        "CosmologicalConstantReceipt is inhabited only modulo explicit external input tokens"
        ∷ "Kaloper-Padilla sequestering v2 is accepted here as a strategy/provenance receipt, not derived from the DASHI carrier"
        ∷ "compact-universe input and sigma shift-symmetry protection are mandatory receipt tokens"
        ∷ "c1 cancellation, c2 Newton calibration, and c3 observational bound are mandatory receipt tokens"
        ∷ []
    }

record WaldReceiptComplete
  (inputs : CosmologicalConstantExplicitInputPack) : Setω where
  field
    status :
      WaldCoefficientSelectionReceiptStatus

    sequesteringReceipt :
      CosmologicalConstantReceipt inputs

    sequesteringReceiptConstructedFromInputs :
      Bool

    sequesteringReceiptConstructedFromInputsIsTrue :
      sequesteringReceiptConstructedFromInputs ≡ true

    c1CancellationToken :
      C1SequesteringCancellationReceiptToken

    c1CancellationTokenFromInputs :
      c1CancellationToken
      ≡
      CosmologicalConstantExplicitInputPack.c1SequesteringCancellation
        inputs

    newtonCalibrationReceipt :
      NewtonCalibrationReceipt

    newtonCalibrationTokenFromInputs :
      NewtonCalibrationReceipt.calibrationToken newtonCalibrationReceipt
      ≡
      CosmologicalConstantExplicitInputPack.c2NewtonCalibration inputs

    cassiniReceipt :
      CassiniReceipt

    cassiniBoundTokenFromInputs :
      CassiniReceipt.observationalBoundToken cassiniReceipt
      ≡
      CosmologicalConstantExplicitInputPack.c3ObservationalBound inputs

    selectedCoefficients :
      List WaldSelectedCoefficient

    selectedCoefficientsAreCanonical :
      selectedCoefficients
      ≡
      canonicalWaldSelectedCoefficients

    c1Selection :
      WaldSelectedCoefficient

    c1SelectionIsSequesteringCancellation :
      c1Selection ≡ selectedC1SequesteringCancellation

    c2Selection :
      WaldSelectedCoefficient

    c2SelectionIsNewtonCalibration :
      c2Selection ≡ selectedC2NewtonObservedCalibration

    c3Selection :
      WaldSelectedCoefficient

    c3SelectionIsZeroWithinCassiniBound :
      c3Selection ≡ selectedC3ZeroWithinCassiniBound

    coefficientValuesSelected :
      Bool

    coefficientValuesSelectedIsTrue :
      coefficientValuesSelected ≡ true

    carrierDerivationClaimed :
      Bool

    carrierDerivationClaimedIsFalse :
      carrierDerivationClaimed ≡ false

    receiptBoundary :
      List String

open WaldReceiptComplete public

waldReceiptCompleteFromExplicitInputs :
  (inputs : CosmologicalConstantExplicitInputPack) →
  WaldReceiptComplete inputs
waldReceiptCompleteFromExplicitInputs inputs =
  record
    { status =
        waldCoefficientsSelectedModuloExplicitInputs
    ; sequesteringReceipt =
        cosmologicalConstantReceiptFromExplicitInputs inputs
    ; sequesteringReceiptConstructedFromInputs =
        true
    ; sequesteringReceiptConstructedFromInputsIsTrue =
        refl
    ; c1CancellationToken =
        CosmologicalConstantExplicitInputPack.c1SequesteringCancellation
          inputs
    ; c1CancellationTokenFromInputs =
        refl
    ; newtonCalibrationReceipt =
        newtonCalibrationReceiptFromToken
          (CosmologicalConstantExplicitInputPack.c2NewtonCalibration inputs)
    ; newtonCalibrationTokenFromInputs =
        refl
    ; cassiniReceipt =
        cassiniReceiptFromToken
          (CosmologicalConstantExplicitInputPack.c3ObservationalBound inputs)
    ; cassiniBoundTokenFromInputs =
        refl
    ; selectedCoefficients =
        canonicalWaldSelectedCoefficients
    ; selectedCoefficientsAreCanonical =
        refl
    ; c1Selection =
        selectedC1SequesteringCancellation
    ; c1SelectionIsSequesteringCancellation =
        refl
    ; c2Selection =
        selectedC2NewtonObservedCalibration
    ; c2SelectionIsNewtonCalibration =
        refl
    ; c3Selection =
        selectedC3ZeroWithinCassiniBound
    ; c3SelectionIsZeroWithinCassiniBound =
        refl
    ; coefficientValuesSelected =
        true
    ; coefficientValuesSelectedIsTrue =
        refl
    ; carrierDerivationClaimed =
        false
    ; carrierDerivationClaimedIsFalse =
        refl
    ; receiptBoundary =
        "WaldReceiptComplete consumes the explicit sequestering input pack"
        ∷ "c1 is cancelled by the sequestering receipt rather than fit as a free vacuum-energy source"
        ∷ "c2 is calibrated by the observed Newton constant"
        ∷ "c3 is selected as zero within the Cassini/PPN observational bound"
        ∷ "the coefficient selection is complete modulo external input tokens and is not a carrier derivation"
        ∷ []
    }

compactUniverseInputMissingHere :
  CompactUniverseInputToken →
  ⊥
compactUniverseInputMissingHere ()

cosmologicalConstantExplicitInputPackMissingHere :
  CosmologicalConstantExplicitInputPack →
  ⊥
cosmologicalConstantExplicitInputPackMissingHere inputs =
  compactUniverseInputMissingHere
    (CosmologicalConstantExplicitInputPack.compactUniverseInput inputs)

record CosmologicalConstantSequesteringReceiptSurface : Setω where
  field
    status :
      CosmologicalConstantSurfaceStatus

    strategyComponents :
      List KaloperPadillaV2StrategyComponent

    strategyComponentsAreCanonical :
      strategyComponents
      ≡
      canonicalKaloperPadillaV2StrategyComponents

    openInputs :
      List CosmologicalConstantOpenInput

    openInputsAreCanonical :
      openInputs
      ≡
      canonicalCosmologicalConstantOpenInputs

    coefficientDisposition :
      CosmologicalConstantWaldCoefficientDispositionSurface

    compactUniverseRequired :
      String

    sequesteringStrategyRequired :
      String

    sigmaProtectionRequired :
      String

    c1CancellationRequired :
      String

    c2NewtonCalibrationRequired :
      String

    c3ObservationalBoundRequired :
      String

    externalProvenanceRequired :
      String

    carrierDerivationClaimed :
      Bool

    carrierDerivationClaimedIsFalse :
      carrierDerivationClaimed ≡ false

    cosmologicalConstantReceiptConstructedHere :
      Bool

    cosmologicalConstantReceiptConstructedHereIsFalse :
      cosmologicalConstantReceiptConstructedHere ≡ false

    noPromotionWithoutAuthority :
      CosmologicalConstantPromotionAuthorityToken →
      ⊥

    receiptBlockedWithoutExplicitInputs :
      CosmologicalConstantExplicitInputPack →
      ⊥

    receiptBoundary :
      List String

open CosmologicalConstantSequesteringReceiptSurface public

canonicalCosmologicalConstantSequesteringReceiptSurface :
  CosmologicalConstantSequesteringReceiptSurface
canonicalCosmologicalConstantSequesteringReceiptSurface =
  record
    { status =
        cosmologicalConstantInputsOnlyNoCarrierDerivation
    ; strategyComponents =
        canonicalKaloperPadillaV2StrategyComponents
    ; strategyComponentsAreCanonical =
        refl
    ; openInputs =
        canonicalCosmologicalConstantOpenInputs
    ; openInputsAreCanonical =
        refl
    ; coefficientDisposition =
        canonicalCosmologicalConstantWaldCoefficientDispositionSurface
    ; compactUniverseRequired =
        "compact-universe/global-volume input token required for sequestering constraints"
    ; sequesteringStrategyRequired =
        "Kaloper-Padilla sequestering v2 strategy token required"
    ; sigmaProtectionRequired =
        "sigma shift-symmetry protection token required"
    ; c1CancellationRequired =
        "c1 cosmological-constant counterterm cancellation requires sequestering receipt"
    ; c2NewtonCalibrationRequired =
        "c2 Einstein-Hilbert/Newton coefficient requires Newton-calibration receipt"
    ; c3ObservationalBoundRequired =
        "c3 residual local-curvature ambiguity requires observational-bound receipt"
    ; externalProvenanceRequired =
        "external theorem/provenance must remain a receipt token and is not derived from carrier structure"
    ; carrierDerivationClaimed =
        false
    ; carrierDerivationClaimedIsFalse =
        refl
    ; cosmologicalConstantReceiptConstructedHere =
        false
    ; cosmologicalConstantReceiptConstructedHereIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; receiptBlockedWithoutExplicitInputs =
        cosmologicalConstantExplicitInputPackMissingHere
    ; receiptBoundary =
        "This surface records the updated cosmological-constant formalism as explicit receipt inputs"
        ∷ "KP sequestering v2, compact universe input, sigma protection, c1 cancellation, c2 calibration, and c3 bound are all external inputs"
        ∷ "No local DASHI carrier theorem or stress-energy bridge derivation is claimed"
        ∷ "Use cosmologicalConstantReceiptFromExplicitInputs only after an adapter supplies the explicit input pack"
        ∷ []
    }
