module DASHI.Physics.Closure.CarrierOS3ReflectionPositivityReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierFactorVecInjectivityOSPositivity as FactorVecOS
import DASHI.Physics.Closure.LatticeMassGapFromTransferMatrixReceipt as TransferGap
import DASHI.Physics.Closure.ReflectionPositivityForWilsonReceipt as WilsonRP

------------------------------------------------------------------------
-- Carrier OS3 / reflection-positivity receipt.
--
-- This receipt records the finite carrier-level OS3 surface by aligning the
-- Wilson reflection-positive lattice receipt with the existing FactorVec
-- transfer-matrix OS-positivity receipt.  It is intentionally fail-closed:
-- no continuum OS package, Wightman reconstruction, uniform continuum gap, or
-- Clay Yang-Mills promotion is introduced here.

data CarrierOS3ReflectionPositivityStatus : Set where
  carrierOS3ReflectionPositivityRecordedFailClosed :
    CarrierOS3ReflectionPositivityStatus

data CarrierOS3SurfacePart : Set where
  finiteWilsonReflectionMap :
    CarrierOS3SurfacePart

  factorVecDepthStepInjectivity :
    CarrierOS3SurfacePart

  carrierTransferMatrixStrictPositivity :
    CarrierOS3SurfacePart

  carrierSchwingerOSPositiveForm :
    CarrierOS3SurfacePart

  continuumPromotionBlocked :
    CarrierOS3SurfacePart

canonicalCarrierOS3SurfaceParts :
  List CarrierOS3SurfacePart
canonicalCarrierOS3SurfaceParts =
  finiteWilsonReflectionMap
  ∷ factorVecDepthStepInjectivity
  ∷ carrierTransferMatrixStrictPositivity
  ∷ carrierSchwingerOSPositiveForm
  ∷ continuumPromotionBlocked
  ∷ []

data CarrierOS3MissingPromotion : Set where

carrierOS3PromotionImpossibleHere :
  CarrierOS3MissingPromotion →
  ⊥
carrierOS3PromotionImpossibleHere ()

carrierOS3ReflectionPositivityStatement : String
carrierOS3ReflectionPositivityStatement =
  "Carrier OS3/reflection positivity is recorded only at the finite carrier level: Wilson finite-lattice reflection positivity aligns with FactorVec depth-step injectivity and transfer-matrix OS positivity; continuum OS, Wightman reconstruction, uniform continuum mass gap, and Clay Yang-Mills promotion remain false."

record CarrierOS3ReflectionPositivityReceipt : Setω where
  field
    status :
      CarrierOS3ReflectionPositivityStatus

    statusIsCanonical :
      status ≡ carrierOS3ReflectionPositivityRecordedFailClosed

    wilsonReflectionReceipt :
      WilsonRP.ReflectionPositivityForWilsonReceipt

    finiteWilsonReflectionPositive :
      WilsonRP.finiteLatticeReflectionPositivityInherited
        wilsonReflectionReceipt
      ≡
      true

    wilsonContinuumReflectionStillFalse :
      WilsonRP.continuumReflectionPositivityProved wilsonReflectionReceipt
      ≡
      false

    factorVecOSReceipt :
      FactorVecOS.CarrierFactorVecInjectivityOSPositivityReceipt

    factorVecCarrierOSPositive :
      FactorVecOS.osPositivityInhabited factorVecOSReceipt ≡ true

    factorVecWightmanStillFalse :
      FactorVecOS.wightmanReconstructionAppliedHere factorVecOSReceipt
      ≡
      false

    factorVecClayStillFalse :
      FactorVecOS.clayYangMillsPromotedHere factorVecOSReceipt
      ≡
      false

    transferMatrixReceipt :
      TransferGap.LatticeMassGapFromTransferMatrixReceipt

    transferMatrixDefined :
      TransferGap.transferMatrixDefined transferMatrixReceipt ≡ true

    finiteTransferGapPositive :
      TransferGap.finiteLatticeGapPositive transferMatrixReceipt ≡ true

    transferUniformContinuumGapStillFalse :
      TransferGap.uniformContinuumGapProved transferMatrixReceipt ≡ false

    carrierOS3SurfaceRecorded :
      Bool

    carrierOS3SurfaceRecordedIsTrue :
      carrierOS3SurfaceRecorded ≡ true

    brstGaugeFixedPositiveHilbertOS3Available :
      Bool

    brstGaugeFixedPositiveHilbertOS3AvailableIsFalse :
      brstGaugeFixedPositiveHilbertOS3Available ≡ false

    ghostUngradedOS3PositiveFormAvailable :
      Bool

    ghostUngradedOS3PositiveFormAvailableIsFalse :
      ghostUngradedOS3PositiveFormAvailable ≡ false

    continuumOSPackagePromoted :
      Bool

    continuumOSPackagePromotedIsFalse :
      continuumOSPackagePromoted ≡ false

    wightmanReconstructionPromoted :
      Bool

    wightmanReconstructionPromotedIsFalse :
      wightmanReconstructionPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    surfaceParts :
      List CarrierOS3SurfacePart

    surfacePartsAreCanonical :
      surfaceParts ≡ canonicalCarrierOS3SurfaceParts

    statement :
      String

    statementIsCanonical :
      statement ≡ carrierOS3ReflectionPositivityStatement

    promotionFlags :
      List CarrierOS3MissingPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open CarrierOS3ReflectionPositivityReceipt public

canonicalCarrierOS3ReflectionPositivityReceipt :
  CarrierOS3ReflectionPositivityReceipt
canonicalCarrierOS3ReflectionPositivityReceipt =
  record
    { status =
        carrierOS3ReflectionPositivityRecordedFailClosed
    ; statusIsCanonical =
        refl
    ; wilsonReflectionReceipt =
        WilsonRP.canonicalReflectionPositivityForWilsonReceipt
    ; finiteWilsonReflectionPositive =
        refl
    ; wilsonContinuumReflectionStillFalse =
        refl
    ; factorVecOSReceipt =
        FactorVecOS.canonicalCarrierFactorVecInjectivityOSPositivityReceipt
    ; factorVecCarrierOSPositive =
        refl
    ; factorVecWightmanStillFalse =
        refl
    ; factorVecClayStillFalse =
        refl
    ; transferMatrixReceipt =
        TransferGap.canonicalLatticeMassGapFromTransferMatrixReceipt
    ; transferMatrixDefined =
        refl
    ; finiteTransferGapPositive =
        refl
    ; transferUniformContinuumGapStillFalse =
        refl
    ; carrierOS3SurfaceRecorded =
        true
    ; carrierOS3SurfaceRecordedIsTrue =
        refl
    ; brstGaugeFixedPositiveHilbertOS3Available =
        false
    ; brstGaugeFixedPositiveHilbertOS3AvailableIsFalse =
        refl
    ; ghostUngradedOS3PositiveFormAvailable =
        false
    ; ghostUngradedOS3PositiveFormAvailableIsFalse =
        refl
    ; continuumOSPackagePromoted =
        false
    ; continuumOSPackagePromotedIsFalse =
        refl
    ; wightmanReconstructionPromoted =
        false
    ; wightmanReconstructionPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; surfaceParts =
        canonicalCarrierOS3SurfaceParts
    ; surfacePartsAreCanonical =
        refl
    ; statement =
        carrierOS3ReflectionPositivityStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Consumes ReflectionPositivityForWilsonReceipt for finite Wilson reflection positivity"
        ∷ "Consumes CarrierFactorVecInjectivityOSPositivity for FactorVec depth-step transfer-matrix OS positivity"
        ∷ "Consumes LatticeMassGapFromTransferMatrixReceipt only at finite-lattice transfer-matrix scope"
        ∷ "The recorded OS3 surface is carrier-level and ungauge-fixed"
        ∷ "BRST gauge-fixed positive-Hilbert OS3 and ungraded ghost OS3 positivity are not constructed"
        ∷ "No continuum OS package, Wightman reconstruction, Clay Yang-Mills, or terminal Clay promotion follows"
        ∷ []
    }

carrierOS3ReflectionPositivityRecorded :
  carrierOS3SurfaceRecorded canonicalCarrierOS3ReflectionPositivityReceipt
  ≡
  true
carrierOS3ReflectionPositivityRecorded =
  refl

carrierOS3ReflectionPositivityKeepsContinuumOSFalse :
  continuumOSPackagePromoted canonicalCarrierOS3ReflectionPositivityReceipt
  ≡
  false
carrierOS3ReflectionPositivityKeepsContinuumOSFalse =
  refl

carrierOS3ReflectionPositivityKeepsWightmanFalse :
  wightmanReconstructionPromoted canonicalCarrierOS3ReflectionPositivityReceipt
  ≡
  false
carrierOS3ReflectionPositivityKeepsWightmanFalse =
  refl

carrierOS3ReflectionPositivityKeepsClayFalse :
  clayYangMillsPromoted canonicalCarrierOS3ReflectionPositivityReceipt
  ≡
  false
carrierOS3ReflectionPositivityKeepsClayFalse =
  refl

carrierOS3ReflectionPositivityKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalCarrierOS3ReflectionPositivityReceipt
  ≡
  false
carrierOS3ReflectionPositivityKeepsTerminalFalse =
  refl
