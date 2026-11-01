module DASHI.Physics.Closure.HEPDataMassKernelCalibrationDiagnostic where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Sum using (inj₂; _⊎_)

open import DASHI.Physics.Closure.HEPDataObservableDefinitionReceipt

------------------------------------------------------------------------
-- HEP-R46: mass-kernel calibration diagnostic.
--
-- This is a non-promoting diagnostic surface that records the remaining gap
-- for neutral-current mass-kernel calibration in the t43/t45 ratio lanes.
--
-- The observed mean values force a non-trivial mass dependence in the current
-- observed windows, which blocks a single constant K shared across t43/t45.
-- The first executable HEP-R46 correction adds a gamma/Z above-pole tail
-- factor.  It preserves the solved t43 scale but leaves t45 as a shape
-- diagnostic rather than an accepted holdout pass.
-- HEP-R47 adds a bounded signed-log high-mass shape direction diagnostic,
-- improving t45 but still not reaching the comparison-law threshold.
-- HEP-R48 then tests five-point bin integration.  It changes t45 only
-- slightly, so the remaining blocker is not primarily midpoint bias in the
-- wide phi-star bins.
-- HEP-R49 tests a flat-photon plus Z-like Sudakov two-component shape.  Under
-- the current component fractions it is also nearly a no-op, because the
-- 106-170 window remains computed as almost entirely Z-like.
-- The file is intentionally explicit about this and does not provide a W3/W4/W5/W8
-- promotion proof.

data HEPDataMassKernelStatus : Set where
  fullyDerived : HEPDataMassKernelStatus
  pdfRequired : HEPDataMassKernelStatus
  parameterFitted : HEPDataMassKernelStatus

record HEPDataMassKernelCalibrationDiagnostic : Set where
  field
    -- Observable-level values from HEP-R45 header receipt.
    t43MeanData : Float
    t45MeanData : Float
    t43MeanDashiV3 : Float

    -- Data-implied neutral-current factors.
    -- K_needed_t43 := t43MeanData / BW(50-76)/BW(76-106)
    -- K_needed_t45 := t45MeanData / BW(106-170)/BW(76-106)
    kNeededT43 : Float
    kNeededT45 : Float

    -- Executable HEP-R46 diagnostic after adding
    -- sigma_dashi.neutral_current_window_factor.
    pureBWRatioT43 : Float
    pureBWRatioT45 : Float
    neutralCurrentRatioT43 : Float
    neutralCurrentRatioT45 : Float
    aboveZTailFactorT45 : Float
    t43Chi2PerDofAfterTail : Float
    t45Chi2PerDofAfterTail : Float
    t45Chi2PerDofAfterDirection : Float
    t45MeanPredDataAfterDirection : Float
    t43Chi2PerDofAfterBinIntegration : Float
    t45Chi2PerDofAfterBinIntegration : Float
    t45MeanPredDataAfterBinIntegration : Float
    t45PhotonFractionAfterTwoComponent : Float
    t43Chi2PerDofAfterTwoComponent : Float
    t45Chi2PerDofAfterTwoComponent : Float
    t45MeanPredDataAfterTwoComponent : Float

    -- Local carrier capability scan result (placeholder for now).
    dashiPDFCarrier : Bool

    massKernelStatus : HEPDataMassKernelStatus

    -- Governance acceptance boundary:
    -- parameter-fitted status is insufficient for W3 comparison-law receipt.
    governanceNote :
      massKernelStatus ≡ fullyDerived ⊎ massKernelStatus ≡ pdfRequired

    -- Explicit non-promotion boundary, recorded for lane alignment.
    boundaryNoPromotion :
      ⊤

canonicalHEPDataMassKernelCalibrationDiagnostic : HEPDataMassKernelCalibrationDiagnostic
canonicalHEPDataMassKernelCalibrationDiagnostic =
  record
    { t43MeanData = 0.046903
    ; t45MeanData = 0.026288
    ; t43MeanDashiV3 = 0.047
    ; kNeededT43 = 1.0438270461
    ; kNeededT45 = 2.5839044637
    ; pureBWRatioT43 = 0.0449335518
    ; pureBWRatioT45 = 0.0101732422
    ; neutralCurrentRatioT43 = 0.0124668829
    ; neutralCurrentRatioT45 = 0.0298575065
    ; aboveZTailFactorT45 = 2.9349056834
    ; t43Chi2PerDofAfterTail = 1.7408778006
    ; t45Chi2PerDofAfterTail = 289.0582788838
    ; t45Chi2PerDofAfterDirection = 16.1225593070
    ; t45MeanPredDataAfterDirection = 0.9587136559
    ; t43Chi2PerDofAfterBinIntegration = 2.1565191176
    ; t45Chi2PerDofAfterBinIntegration = 15.8545837677
    ; t45MeanPredDataAfterBinIntegration = 0.9581222335
    ; t45PhotonFractionAfterTwoComponent = 0.0000379589
    ; t43Chi2PerDofAfterTwoComponent = 2.1565191176
    ; t45Chi2PerDofAfterTwoComponent = 15.8542832674
    ; t45MeanPredDataAfterTwoComponent = 0.9581304397
    ; dashiPDFCarrier = false
    ; massKernelStatus = pdfRequired
    ; governanceNote = inj₂ refl
    ; boundaryNoPromotion = tt
    }
