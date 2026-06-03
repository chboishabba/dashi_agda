module DASHI.Physics.Closure.ClayNumericPrecisionCorrectionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat; _-_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.ClaySolvedLedgerLemmas as Solved
import DASHI.Physics.Closure.YMBalabanMarginSplitReceipt as Margin
import DASHI.Physics.Closure.PhysicalSSPSpreadBoundAttemptReceipt as Spread

------------------------------------------------------------------------
-- Clay numeric precision correction.
--
-- This receipt records the sharper numeric ledger behind the coarse
-- hundredths-level solved ledger.  It does not replace the earlier coarse
-- constants; it records the precision convention and the exact places where
-- a rounded threshold is safe, borderline, or merely a mnemonic.

data PrecisionCorrectionStatus : Set where
  clayNumericPrecisionCorrectionRecorded_noPromotion :
    PrecisionCorrectionStatus

data PrecisionWorker : Set where
  w2YMPrecision :
    PrecisionWorker

  w5Gate3TaperPrecision :
    PrecisionWorker

  w6GovernancePrecision :
    PrecisionWorker

canonicalPrecisionWorkers : List PrecisionWorker
canonicalPrecisionWorkers =
  w2YMPrecision
  ∷ w5Gate3TaperPrecision
  ∷ w6GovernancePrecision
  ∷ []

data PrecisionNonClaim : Set where
  connectedAnimalConvergenceIsNotBalabanSeed :
    PrecisionNonClaim

  btTreePrecisionDoesNotProveBalabanTransfer :
    PrecisionNonClaim

  strictNumericMarginDoesNotProveRGFlow :
    PrecisionNonClaim

  pawotgSeriesMarginDoesNotProvePhysicalEmbedding :
    PrecisionNonClaim

  oneDensityGate3SeriesIsNotThreeDensityGravitySeries :
    PrecisionNonClaim

  noClayPromotion :
    PrecisionNonClaim

canonicalPrecisionNonClaims : List PrecisionNonClaim
canonicalPrecisionNonClaims =
  connectedAnimalConvergenceIsNotBalabanSeed
  ∷ btTreePrecisionDoesNotProveBalabanTransfer
  ∷ strictNumericMarginDoesNotProveRGFlow
  ∷ pawotgSeriesMarginDoesNotProvePhysicalEmbedding
  ∷ oneDensityGate3SeriesIsNotThreeDensityGravitySeries
  ∷ noClayPromotion
  ∷ []

data PrecisionPromotion : Set where

precisionPromotionImpossibleHere :
  PrecisionPromotion →
  ⊥
precisionPromotionImpossibleHere ()

------------------------------------------------------------------------
-- Millionths-scaled beta thresholds and gaps.

betaScaleMillionths : Nat
betaScaleMillionths =
  1000000

physicalBetaMillionths : Nat
physicalBetaMillionths =
  6000000

connectedAnimalThresholdMillionths : Nat
connectedAnimalThresholdMillionths =
  9593637

connectedAnimalGapMillionths : Nat
connectedAnimalGapMillionths =
  connectedAnimalThresholdMillionths - physicalBetaMillionths

btTreeThresholdMillionths : Nat
btTreeThresholdMillionths =
  10130860

btTreeGapMillionths : Nat
btTreeGapMillionths =
  btTreeThresholdMillionths - physicalBetaMillionths

strictAbsorptionThresholdMillionths : Nat
strictAbsorptionThresholdMillionths =
  13631603

strictAbsorptionGapMillionths : Nat
strictAbsorptionGapMillionths =
  strictAbsorptionThresholdMillionths - physicalBetaMillionths

strictSafeSampleMillionths : Nat
strictSafeSampleMillionths =
  13640000

strictSafeSampleMinusThresholdMillionths : Nat
strictSafeSampleMinusThresholdMillionths =
  strictSafeSampleMillionths - strictAbsorptionThresholdMillionths

t7aDirectThresholdHundredths : Nat
t7aDirectThresholdHundredths =
  1656

t7aDirectGapHundredths : Nat
t7aDirectGapHundredths =
  t7aDirectThresholdHundredths - 600

connectedAnimalThresholdMillionthsIs9593637 :
  connectedAnimalThresholdMillionths ≡ 9593637
connectedAnimalThresholdMillionthsIs9593637 =
  refl

connectedAnimalGapMillionthsIs3593637 :
  connectedAnimalGapMillionths ≡ 3593637
connectedAnimalGapMillionthsIs3593637 =
  refl

btTreeThresholdMillionthsIs10130860 :
  btTreeThresholdMillionths ≡ 10130860
btTreeThresholdMillionthsIs10130860 =
  refl

btTreeGapMillionthsIs4130860 :
  btTreeGapMillionths ≡ 4130860
btTreeGapMillionthsIs4130860 =
  refl

strictAbsorptionThresholdMillionthsIs13631603 :
  strictAbsorptionThresholdMillionths ≡ 13631603
strictAbsorptionThresholdMillionthsIs13631603 =
  refl

strictAbsorptionGapMillionthsIs7631603 :
  strictAbsorptionGapMillionths ≡ 7631603
strictAbsorptionGapMillionthsIs7631603 =
  refl

strictSafeSampleMinusThresholdMillionthsIs8397 :
  strictSafeSampleMinusThresholdMillionths ≡ 8397
strictSafeSampleMinusThresholdMillionthsIs8397 =
  refl

t7aDirectGapHundredthsIs1056 :
  t7aDirectGapHundredths ≡ 1056
t7aDirectGapHundredthsIs1056 =
  refl

------------------------------------------------------------------------
-- Gate3 one-density PAWOTG precision.

sigmaScaleMillionths : Nat
sigmaScaleMillionths =
  1000000

seriesScaleBillionths : Nat
seriesScaleBillionths =
  1000000000

sigmaDigitMillionths : Nat
sigmaDigitMillionths =
  288675

sigmaPhysicalTargetMillionths : Nat
sigmaPhysicalTargetMillionths =
  302511

sigmaOneDensityCriticalMillionths : Nat
sigmaOneDensityCriticalMillionths =
  505208

sigmaPhysicalHeadroomMillionths : Nat
sigmaPhysicalHeadroomMillionths =
  sigmaPhysicalTargetMillionths - sigmaDigitMillionths

sigmaOneDensityCriticalHeadroomMillionths : Nat
sigmaOneDensityCriticalHeadroomMillionths =
  sigmaOneDensityCriticalMillionths - sigmaDigitMillionths

gate3OneDensitySeriesAtSigmaDigitBillionths : Nat
gate3OneDensitySeriesAtSigmaDigitBillionths =
  80284628

gate3OneDensitySeriesAtPhysicalTargetBillionths : Nat
gate3OneDensitySeriesAtPhysicalTargetBillionths =
  110976368

sigmaPhysicalHeadroomMillionthsIs13836 :
  sigmaPhysicalHeadroomMillionths ≡ 13836
sigmaPhysicalHeadroomMillionthsIs13836 =
  refl

sigmaOneDensityCriticalHeadroomMillionthsIs216533 :
  sigmaOneDensityCriticalHeadroomMillionths ≡ 216533
sigmaOneDensityCriticalHeadroomMillionthsIs216533 =
  refl

gate3OneDensitySeriesAtSigmaDigitBillionthsIs80284628 :
  gate3OneDensitySeriesAtSigmaDigitBillionths ≡ 80284628
gate3OneDensitySeriesAtSigmaDigitBillionthsIs80284628 =
  refl

gate3OneDensitySeriesAtPhysicalTargetBillionthsIs110976368 :
  gate3OneDensitySeriesAtPhysicalTargetBillionths ≡ 110976368
gate3OneDensitySeriesAtPhysicalTargetBillionthsIs110976368 =
  refl

------------------------------------------------------------------------
-- Boundary text.

precisionCorrectionSummary : String
precisionCorrectionSummary =
  "Precision correction: connected-animal KP threshold is 9.593637, not the rounded 9.59 safe statement; p=7 BT-tree with a=0.06 and c_min=0.198 is 10.13086; strict absorption is 13.631603, so beta=13.64 is barely but safely above it. Gate3 one-density PAWOTG gives S(sigma_digit)=0.080284628, S(0.302511)=0.110976368, and sigma_crit=0.505208; the open issue remains the physical 3D SSP/Hecke embedding."

precisionCorrectionBoundary : String
precisionCorrectionBoundary =
  "This precision receipt records numeric ledger refinements only. It does not prove nonperturbative Balaban transfer, physical SSP spread, uniform frame lower bound, Navier-Stokes dominance, or any Clay theorem."

record ClayNumericPrecisionCorrectionReceipt : Setω where
  field
    status :
      PrecisionCorrectionStatus

    statusIsCanonical :
      status ≡ clayNumericPrecisionCorrectionRecorded_noPromotion

    solvedLedgerCoarse :
      Solved.connectedAnimalThreshold ≡ 959

    solvedLedgerBTTreeCorrected :
      Solved.btTreeThreshold ≡ 1013

    solvedLedgerT7ADemoted :
      Solved.t7aDirectCountingAllowedAsPrimary ≡ false

    marginReceipt :
      Margin.YMBalabanMarginSplitReceipt

    marginStrictSeedStillRequired :
      Margin.strictAbsorptionRequiredForBalabanSeed marginReceipt ≡ true

    marginBalabanTransferStillOpen :
      Margin.balabanTransferProvedHere marginReceipt ≡ false

    spreadReceipt :
      Spread.PhysicalSSPSpreadBoundAttemptReceipt

    spreadPhysicalEmbeddingStillOpen :
      Spread.physicalSSPEmbedding3DProved spreadReceipt ≡ false

    spreadGate3StillOpen :
      Spread.gate3Closed spreadReceipt ≡ false

    workers :
      List PrecisionWorker

    workersAreCanonical :
      workers ≡ canonicalPrecisionWorkers

    nonClaims :
      List PrecisionNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalPrecisionNonClaims

    caThresholdPrecise :
      Nat

    caThresholdPreciseIs9593637 :
      caThresholdPrecise ≡ connectedAnimalThresholdMillionths

    caGapPrecise :
      Nat

    caGapPreciseIs3593637 :
      caGapPrecise ≡ connectedAnimalGapMillionths

    btThresholdPrecise :
      Nat

    btThresholdPreciseIs10130860 :
      btThresholdPrecise ≡ btTreeThresholdMillionths

    btGapPrecise :
      Nat

    btGapPreciseIs4130860 :
      btGapPrecise ≡ btTreeGapMillionths

    strictThresholdPrecise :
      Nat

    strictThresholdPreciseIs13631603 :
      strictThresholdPrecise ≡ strictAbsorptionThresholdMillionths

    strictGapPrecise :
      Nat

    strictGapPreciseIs7631603 :
      strictGapPrecise ≡ strictAbsorptionGapMillionths

    strictSampleSafetyMargin :
      Nat

    strictSampleSafetyMarginIs8397 :
      strictSampleSafetyMargin ≡ strictSafeSampleMinusThresholdMillionths

    gate3OneDensitySeriesDigit :
      Nat

    gate3OneDensitySeriesDigitIs80284628 :
      gate3OneDensitySeriesDigit
      ≡
      gate3OneDensitySeriesAtSigmaDigitBillionths

    gate3OneDensitySeriesTarget :
      Nat

    gate3OneDensitySeriesTargetIs110976368 :
      gate3OneDensitySeriesTarget
      ≡
      gate3OneDensitySeriesAtPhysicalTargetBillionths

    gate3OneDensityCriticalSigma :
      Nat

    gate3OneDensityCriticalSigmaIs505208 :
      gate3OneDensityCriticalSigma
      ≡
      sigmaOneDensityCriticalMillionths

    gate3PhysicalTargetHeadroom :
      Nat

    gate3PhysicalTargetHeadroomIs13836 :
      gate3PhysicalTargetHeadroom
      ≡
      sigmaPhysicalHeadroomMillionths

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    gate3Closed :
      Bool

    gate3ClosedIsFalse :
      gate3Closed ≡ false

    receiptBoundary :
      List String

canonicalClayNumericPrecisionCorrectionReceipt :
  ClayNumericPrecisionCorrectionReceipt
canonicalClayNumericPrecisionCorrectionReceipt =
  record
    { status =
        clayNumericPrecisionCorrectionRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; solvedLedgerCoarse =
        refl
    ; solvedLedgerBTTreeCorrected =
        refl
    ; solvedLedgerT7ADemoted =
        refl
    ; marginReceipt =
        Margin.canonicalYMBalabanMarginSplitReceipt
    ; marginStrictSeedStillRequired =
        refl
    ; marginBalabanTransferStillOpen =
        refl
    ; spreadReceipt =
        Spread.canonicalPhysicalSSPSpreadBoundAttemptReceipt
    ; spreadPhysicalEmbeddingStillOpen =
        refl
    ; spreadGate3StillOpen =
        refl
    ; workers =
        canonicalPrecisionWorkers
    ; workersAreCanonical =
        refl
    ; nonClaims =
        canonicalPrecisionNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; caThresholdPrecise =
        connectedAnimalThresholdMillionths
    ; caThresholdPreciseIs9593637 =
        refl
    ; caGapPrecise =
        connectedAnimalGapMillionths
    ; caGapPreciseIs3593637 =
        refl
    ; btThresholdPrecise =
        btTreeThresholdMillionths
    ; btThresholdPreciseIs10130860 =
        refl
    ; btGapPrecise =
        btTreeGapMillionths
    ; btGapPreciseIs4130860 =
        refl
    ; strictThresholdPrecise =
        strictAbsorptionThresholdMillionths
    ; strictThresholdPreciseIs13631603 =
        refl
    ; strictGapPrecise =
        strictAbsorptionGapMillionths
    ; strictGapPreciseIs7631603 =
        refl
    ; strictSampleSafetyMargin =
        strictSafeSampleMinusThresholdMillionths
    ; strictSampleSafetyMarginIs8397 =
        refl
    ; gate3OneDensitySeriesDigit =
        gate3OneDensitySeriesAtSigmaDigitBillionths
    ; gate3OneDensitySeriesDigitIs80284628 =
        refl
    ; gate3OneDensitySeriesTarget =
        gate3OneDensitySeriesAtPhysicalTargetBillionths
    ; gate3OneDensitySeriesTargetIs110976368 =
        refl
    ; gate3OneDensityCriticalSigma =
        sigmaOneDensityCriticalMillionths
    ; gate3OneDensityCriticalSigmaIs505208 =
        refl
    ; gate3PhysicalTargetHeadroom =
        sigmaPhysicalHeadroomMillionths
    ; gate3PhysicalTargetHeadroomIs13836 =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; gate3Closed =
        false
    ; gate3ClosedIsFalse =
        refl
    ; receiptBoundary =
        precisionCorrectionBoundary
        ∷ "Use beta > 9.593637 for connected-animal KP convergence."
        ∷ "Use beta*c_min-a>log(2p), or a robust sample such as beta >= 13.7, for strict Balaban seed statements."
        ∷ "Do not use the connected-animal 3.593637 gap as a Balaban-induction proof."
        ∷ "Gate3 one-density PAWOTG arithmetic has slack; the missing theorem is physical 3D SSP/Hecke embedding transport."
        ∷ "All Clay and Gate3 promotions remain false."
        ∷ []
    }

canonicalClayNumericPrecisionKeepsPromotionsFalse :
  ClayNumericPrecisionCorrectionReceipt.clayYangMillsPromoted
    canonicalClayNumericPrecisionCorrectionReceipt
  ≡
  false
canonicalClayNumericPrecisionKeepsPromotionsFalse =
  refl
