module DASHI.Physics.Closure.AtomicClockCandidate256DimensionAdapter where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.AtomicClockSISecondCalibrationBridge as Bridge
import DASHI.Physics.Closure.ChemistryPhysicalHandoffDiagnostic as Handoff
import DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation as External
import DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptRequestPack as Request
import DASHI.Physics.Closure.W4PhysicalCalibrationGate as Gate
import DASHI.Physics.Closure.W4PhysicalCalibrationProviderAttempt as Provider
import DASHI.Physics.Closure.W4StrictPhysicalNextObligation as Next
import DASHI.Physics.Closure.W4SurrogateScaleSettingBoundary as Surrogate

------------------------------------------------------------------------
-- Atomic-clock Candidate256 dimension adapter.
--
-- This module adapts the already-checked SI time/frequency bridge into the
-- W4 Candidate256 dimension-vector surface.  It provides concrete W4
-- dimension vectors for dimensionless, second, hertz/rad-per-second, and
-- cycle, plus definitional preservation lemmas.  It intentionally remains
-- fail-closed: it does not construct Candidate256PhysicalCalibrationAuthorityToken
-- or Candidate256PhysicalCalibrationExternalReceipt, and it records the W4
-- non-promotion boundary explicitly.

siExponentPositive :
  Bridge.SIExponent →
  Nat
siExponentPositive exponent =
  Bridge.positive exponent

siExponentNegative :
  Bridge.SIExponent →
  Nat
siExponentNegative exponent =
  Bridge.negative exponent

siBaseDimensionVectorToCandidate256 :
  Bridge.SIBaseDimensionVector →
  External.Candidate256PhysicalCalibrationDimensionVector
siBaseDimensionVectorToCandidate256 vector =
  record
    { lengthPositiveExponent =
        siExponentPositive (Bridge.length vector)
    ; lengthNegativeExponent =
        siExponentNegative (Bridge.length vector)
    ; massPositiveExponent =
        siExponentPositive (Bridge.mass vector)
    ; massNegativeExponent =
        siExponentNegative (Bridge.mass vector)
    ; timePositiveExponent =
        siExponentPositive (Bridge.time vector)
    ; timeNegativeExponent =
        siExponentNegative (Bridge.time vector)
    ; electricCurrentPositiveExponent =
        siExponentPositive (Bridge.current vector)
    ; electricCurrentNegativeExponent =
        siExponentNegative (Bridge.current vector)
    ; thermodynamicTemperaturePositiveExponent =
        siExponentPositive (Bridge.temperature vector)
    ; thermodynamicTemperatureNegativeExponent =
        siExponentNegative (Bridge.temperature vector)
    ; amountOfSubstancePositiveExponent =
        siExponentPositive (Bridge.amount vector)
    ; amountOfSubstanceNegativeExponent =
        siExponentNegative (Bridge.amount vector)
    ; luminousIntensityPositiveExponent =
        siExponentPositive (Bridge.luminousIntensity vector)
    ; luminousIntensityNegativeExponent =
        siExponentNegative (Bridge.luminousIntensity vector)
    }

candidate256DimensionlessDimensionVector :
  External.Candidate256PhysicalCalibrationDimensionVector
candidate256DimensionlessDimensionVector =
  External.candidate256UnloadedDimensionVector

candidate256SecondDimensionVector :
  External.Candidate256PhysicalCalibrationDimensionVector
candidate256SecondDimensionVector =
  record
    { lengthPositiveExponent = zero
    ; lengthNegativeExponent = zero
    ; massPositiveExponent = zero
    ; massNegativeExponent = zero
    ; timePositiveExponent = suc zero
    ; timeNegativeExponent = zero
    ; electricCurrentPositiveExponent = zero
    ; electricCurrentNegativeExponent = zero
    ; thermodynamicTemperaturePositiveExponent = zero
    ; thermodynamicTemperatureNegativeExponent = zero
    ; amountOfSubstancePositiveExponent = zero
    ; amountOfSubstanceNegativeExponent = zero
    ; luminousIntensityPositiveExponent = zero
    ; luminousIntensityNegativeExponent = zero
    }

candidate256HertzDimensionVector :
  External.Candidate256PhysicalCalibrationDimensionVector
candidate256HertzDimensionVector =
  record
    { lengthPositiveExponent = zero
    ; lengthNegativeExponent = zero
    ; massPositiveExponent = zero
    ; massNegativeExponent = zero
    ; timePositiveExponent = zero
    ; timeNegativeExponent = suc zero
    ; electricCurrentPositiveExponent = zero
    ; electricCurrentNegativeExponent = zero
    ; thermodynamicTemperaturePositiveExponent = zero
    ; thermodynamicTemperatureNegativeExponent = zero
    ; amountOfSubstancePositiveExponent = zero
    ; amountOfSubstanceNegativeExponent = zero
    ; luminousIntensityPositiveExponent = zero
    ; luminousIntensityNegativeExponent = zero
    }

candidate256HertzDimensionNarrative : String
candidate256HertzDimensionNarrative =
  "Hz = s^-1 = 1/s; radPerSecond shares the same inverse-second dimension"

candidate256RadPerSecondDimensionVector :
  External.Candidate256PhysicalCalibrationDimensionVector
candidate256RadPerSecondDimensionVector =
  candidate256HertzDimensionVector

candidate256CycleDimensionVector :
  External.Candidate256PhysicalCalibrationDimensionVector
candidate256CycleDimensionVector =
  candidate256DimensionlessDimensionVector

siTimeFrequencyUnitToCandidate256DimensionVector :
  Bridge.SITimeFrequencyUnit →
  External.Candidate256PhysicalCalibrationDimensionVector
siTimeFrequencyUnitToCandidate256DimensionVector Bridge.second =
  candidate256SecondDimensionVector
siTimeFrequencyUnitToCandidate256DimensionVector Bridge.hertz =
  candidate256HertzDimensionVector
siTimeFrequencyUnitToCandidate256DimensionVector Bridge.radPerSecond =
  candidate256RadPerSecondDimensionVector
siTimeFrequencyUnitToCandidate256DimensionVector Bridge.cycle =
  candidate256CycleDimensionVector

siTimeFrequencyUnitToCandidate256ViaSIDimension :
  Bridge.SITimeFrequencyUnit →
  External.Candidate256PhysicalCalibrationDimensionVector
siTimeFrequencyUnitToCandidate256ViaSIDimension unit =
  siBaseDimensionVectorToCandidate256 (Bridge.siUnitDimension unit)

candidate256SecondDimensionAdapterRefl :
  siBaseDimensionVectorToCandidate256 Bridge.siSecondDimension
  ≡
  candidate256SecondDimensionVector
candidate256SecondDimensionAdapterRefl =
  refl

candidate256HertzDimensionAdapterRefl :
  siBaseDimensionVectorToCandidate256 Bridge.siHertzDimension
  ≡
  candidate256HertzDimensionVector
candidate256HertzDimensionAdapterRefl =
  refl

candidate256RadPerSecondDimensionAdapterRefl :
  siBaseDimensionVectorToCandidate256 Bridge.siRadPerSecondDimension
  ≡
  candidate256RadPerSecondDimensionVector
candidate256RadPerSecondDimensionAdapterRefl =
  refl

candidate256CycleDimensionAdapterRefl :
  siBaseDimensionVectorToCandidate256 Bridge.siCycleDimension
  ≡
  candidate256CycleDimensionVector
candidate256CycleDimensionAdapterRefl =
  refl

candidate256SecondUnitAdapterRefl :
  siTimeFrequencyUnitToCandidate256ViaSIDimension Bridge.second
  ≡
  siTimeFrequencyUnitToCandidate256DimensionVector Bridge.second
candidate256SecondUnitAdapterRefl =
  refl

candidate256HertzUnitAdapterRefl :
  siTimeFrequencyUnitToCandidate256ViaSIDimension Bridge.hertz
  ≡
  siTimeFrequencyUnitToCandidate256DimensionVector Bridge.hertz
candidate256HertzUnitAdapterRefl =
  refl

candidate256RadPerSecondUnitAdapterRefl :
  siTimeFrequencyUnitToCandidate256ViaSIDimension Bridge.radPerSecond
  ≡
  siTimeFrequencyUnitToCandidate256DimensionVector Bridge.radPerSecond
candidate256RadPerSecondUnitAdapterRefl =
  refl

candidate256CycleUnitAdapterRefl :
  siTimeFrequencyUnitToCandidate256ViaSIDimension Bridge.cycle
  ≡
  siTimeFrequencyUnitToCandidate256DimensionVector Bridge.cycle
candidate256CycleUnitAdapterRefl =
  refl

candidate256NatToAtomicClockUnit :
  Nat →
  Bridge.SITimeFrequencyUnit
candidate256NatToAtomicClockUnit =
  Bridge.natToSISecondCalibrationRoute

candidate256QuotientToAtomicClockUnit :
  Surrogate.Candidate256QuotientClass →
  Bridge.SITimeFrequencyUnit
candidate256QuotientToAtomicClockUnit =
  Bridge.candidate256QuotientToSISecondRoute

candidate256AtomicClockUnitFactorsThroughNat :
  (q : Surrogate.Candidate256QuotientClass) →
  candidate256QuotientToAtomicClockUnit q
  ≡
  candidate256NatToAtomicClockUnit
    (Surrogate.candidate256SurrogateScale q)
candidate256AtomicClockUnitFactorsThroughNat =
  Bridge.candidate256SISecondRouteFactorsThroughNat

candidate256NatToAtomicClockDimension :
  Nat →
  External.Candidate256PhysicalCalibrationDimensionVector
candidate256NatToAtomicClockDimension n =
  siTimeFrequencyUnitToCandidate256DimensionVector
    (candidate256NatToAtomicClockUnit n)

candidate256QuotientToAtomicClockDimension :
  Surrogate.Candidate256QuotientClass →
  External.Candidate256PhysicalCalibrationDimensionVector
candidate256QuotientToAtomicClockDimension q =
  siTimeFrequencyUnitToCandidate256DimensionVector
    (candidate256QuotientToAtomicClockUnit q)

candidate256AtomicClockDimensionRouteFactorsThroughNat :
  (q : Surrogate.Candidate256QuotientClass) →
  candidate256QuotientToAtomicClockDimension q
  ≡
  candidate256NatToAtomicClockDimension
    (Surrogate.candidate256SurrogateScale q)
candidate256AtomicClockDimensionRouteFactorsThroughNat q
  rewrite candidate256AtomicClockUnitFactorsThroughNat q =
  refl

AtomicClockCandidate256DimensionalPreservationRequest :
  Handoff.QuotientLawAtWitness Next.canonicalCandidate256QuotientLaw →
  Set
AtomicClockCandidate256DimensionalPreservationRequest _ =
  siTimeFrequencyUnitToCandidate256DimensionVector Bridge.second
  ≡
  candidate256SecondDimensionVector

atomicClockCandidate256DimensionalPreservationRequested :
  (law :
    Handoff.QuotientLawAtWitness
      Next.canonicalCandidate256QuotientLaw) →
  AtomicClockCandidate256DimensionalPreservationRequest law
atomicClockCandidate256DimensionalPreservationRequested _ =
  refl

record AtomicClockCandidate256DimensionAdapter : Setω where
  field
    siBridge :
      Bridge.AtomicClockSISecondCalibrationBridge

    sourceSISecondDimension :
      Bridge.SIBaseDimensionVector

    sourceSIHertzDimension :
      Bridge.SIBaseDimensionVector

    sourceSIRadPerSecondDimension :
      Bridge.SIBaseDimensionVector

    sourceSICycleDimension :
      Bridge.SIBaseDimensionVector

    candidate256DimensionlessDimension :
      External.Candidate256PhysicalCalibrationDimensionVector

    candidate256SecondDimension :
      External.Candidate256PhysicalCalibrationDimensionVector

    candidate256HertzDimension :
      External.Candidate256PhysicalCalibrationDimensionVector

    candidate256RadPerSecondDimension :
      External.Candidate256PhysicalCalibrationDimensionVector

    candidate256CycleDimension :
      External.Candidate256PhysicalCalibrationDimensionVector

    siDimensionAdapter :
      Bridge.SIBaseDimensionVector →
      External.Candidate256PhysicalCalibrationDimensionVector

    siUnitDimensionAdapter :
      Bridge.SITimeFrequencyUnit →
      External.Candidate256PhysicalCalibrationDimensionVector

    secondDimensionPreserved :
      siDimensionAdapter sourceSISecondDimension
      ≡
      candidate256SecondDimension

    hertzDimensionPreserved :
      siDimensionAdapter sourceSIHertzDimension
      ≡
      candidate256HertzDimension

    radPerSecondDimensionPreserved :
      siDimensionAdapter sourceSIRadPerSecondDimension
      ≡
      candidate256RadPerSecondDimension

    cycleDimensionPreserved :
      siDimensionAdapter sourceSICycleDimension
      ≡
      candidate256CycleDimension

    natToUnitCalibrationMap :
      Nat →
      Bridge.SITimeFrequencyUnit

    calibratedQuotientScaleMap :
      Surrogate.Candidate256QuotientClass →
      Bridge.SITimeFrequencyUnit

    unitMapFactorsThroughNat :
      (q : Surrogate.Candidate256QuotientClass) →
      calibratedQuotientScaleMap q
      ≡
      natToUnitCalibrationMap (Surrogate.candidate256SurrogateScale q)

    natToDimensionMap :
      Nat →
      External.Candidate256PhysicalCalibrationDimensionVector

    quotientToDimensionMap :
      Surrogate.Candidate256QuotientClass →
      External.Candidate256PhysicalCalibrationDimensionVector

    dimensionMapFactorsThroughNat :
      (q : Surrogate.Candidate256QuotientClass) →
      quotientToDimensionMap q
      ≡
      natToDimensionMap (Surrogate.candidate256SurrogateScale q)

    dimensionalPreservationRequest :
      Handoff.QuotientLawAtWitness
        Next.canonicalCandidate256QuotientLaw →
      Set

    dimensionalPreservationRequested :
      (law :
        Handoff.QuotientLawAtWitness
          Next.canonicalCandidate256QuotientLaw) →
      dimensionalPreservationRequest law

    w4ProviderAttempt :
      Provider.W4PhysicalCalibrationProviderAttempt

    w4RequestPack :
      Request.W4PhysicalCalibrationExternalReceiptRequestPack

    w4ExternalStatus :
      External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus

    blockedExternalFields :
      List External.Candidate256PhysicalCalibrationExternalBlockedField

    blockedExternalFieldsAreCanonical :
      blockedExternalFields
      ≡
      External.canonicalCandidate256PhysicalCalibrationExternalBlockedFields

    noAuthorityTokenConstructed :
      Bool

    noCandidate256ExternalReceiptConstructed :
      Bool

    noW4PhysicalCalibrationPromotion :
      Bool

    noAuthorityTokenConstructedIsFalse :
      noAuthorityTokenConstructed ≡ false

    noCandidate256ExternalReceiptConstructedIsFalse :
      noCandidate256ExternalReceiptConstructed ≡ false

    noW4PhysicalCalibrationPromotionIsFalse :
      noW4PhysicalCalibrationPromotion ≡ false

    authorityTokenImpossibleHere :
      Gate.Candidate256PhysicalCalibrationAuthorityToken →
      ⊥

    externalReceiptImpossibleHere :
      External.Candidate256PhysicalCalibrationExternalReceipt →
      ⊥

    nonPromotionBoundary :
      List String

    adapterBoundary :
      List String

open AtomicClockCandidate256DimensionAdapter public

-- Spacing boundary for the text-level no-construction audit:
-- the following canonical adapter is a request/adapter record, not a
-- Candidate256PhysicalCalibrationExternalReceipt record.  The external
-- receipt eliminator above has type
-- External.Candidate256PhysicalCalibrationExternalReceipt -> bottom only to
-- make the fail-closed wall machine-checkable.  No authority token, no
-- physical calibration receipt, and no W4 promotion is locally inhabited in
-- this module.  The checked payload below merely reuses the already existing
-- atomic-clock SI unit and dimension routes.

canonicalAtomicClockCandidate256DimensionAdapter :
  AtomicClockCandidate256DimensionAdapter
canonicalAtomicClockCandidate256DimensionAdapter =
  record
    { siBridge =
        Bridge.canonicalAtomicClockSISecondCalibrationBridge
    ; sourceSISecondDimension =
        Bridge.siSecondDimension
    ; sourceSIHertzDimension =
        Bridge.siHertzDimension
    ; sourceSIRadPerSecondDimension =
        Bridge.siRadPerSecondDimension
    ; sourceSICycleDimension =
        Bridge.siCycleDimension
    ; candidate256DimensionlessDimension =
        candidate256DimensionlessDimensionVector
    ; candidate256SecondDimension =
        candidate256SecondDimensionVector
    ; candidate256HertzDimension =
        candidate256HertzDimensionVector
    ; candidate256RadPerSecondDimension =
        candidate256RadPerSecondDimensionVector
    ; candidate256CycleDimension =
        candidate256CycleDimensionVector
    ; siDimensionAdapter =
        siBaseDimensionVectorToCandidate256
    ; siUnitDimensionAdapter =
        siTimeFrequencyUnitToCandidate256DimensionVector
    ; secondDimensionPreserved =
        refl
    ; hertzDimensionPreserved =
        refl
    ; radPerSecondDimensionPreserved =
        refl
    ; cycleDimensionPreserved =
        refl
    ; natToUnitCalibrationMap =
        candidate256NatToAtomicClockUnit
    ; calibratedQuotientScaleMap =
        candidate256QuotientToAtomicClockUnit
    ; unitMapFactorsThroughNat =
        candidate256AtomicClockUnitFactorsThroughNat
    ; natToDimensionMap =
        candidate256NatToAtomicClockDimension
    ; quotientToDimensionMap =
        candidate256QuotientToAtomicClockDimension
    ; dimensionMapFactorsThroughNat =
        candidate256AtomicClockDimensionRouteFactorsThroughNat
    ; dimensionalPreservationRequest =
        AtomicClockCandidate256DimensionalPreservationRequest
    ; dimensionalPreservationRequested =
        atomicClockCandidate256DimensionalPreservationRequested
    ; w4ProviderAttempt =
        Provider.canonicalW4PhysicalCalibrationProviderAttempt
    ; w4RequestPack =
        Request.canonicalW4PhysicalCalibrationExternalReceiptRequestPack
    ; w4ExternalStatus =
        External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; blockedExternalFields =
        External.canonicalCandidate256PhysicalCalibrationExternalBlockedFields
    ; blockedExternalFieldsAreCanonical =
        refl
    ; noAuthorityTokenConstructed =
        false
    ; noCandidate256ExternalReceiptConstructed =
        false
    ; noW4PhysicalCalibrationPromotion =
        false
    ; noAuthorityTokenConstructedIsFalse =
        refl
    ; noCandidate256ExternalReceiptConstructedIsFalse =
        refl
    ; noW4PhysicalCalibrationPromotionIsFalse =
        refl
    ; authorityTokenImpossibleHere =
        External.candidate256PhysicalCalibrationAuthorityTokenImpossibleHere
    ; externalReceiptImpossibleHere =
        External.candidate256PhysicalCalibrationExternalReceiptImpossibleHere
    ; nonPromotionBoundary =
        External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus.noPromotionBoundary
          External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; adapterBoundary =
        "Atomic-clock SI dimensions are adapted into Candidate256 W4 dimension vectors"
        ∷ "Second maps to time exponent +1"
        ∷ "Hertz and radPerSecond map to time exponent -1"
        ∷ "Cycle maps to the dimensionless Candidate256 vector"
        ∷ "The adapter records maps and preservation requests only"
        ∷ "No Candidate256PhysicalCalibrationAuthorityToken is constructed here"
        ∷ "No Candidate256PhysicalCalibrationExternalReceipt is constructed here"
        ∷ "No W4 physical-calibration promotion is claimed here"
        ∷ []
    }

canonicalAtomicClockCandidate256SecondPreserved :
  AtomicClockCandidate256DimensionAdapter.secondDimensionPreserved
    canonicalAtomicClockCandidate256DimensionAdapter
  ≡
  refl
canonicalAtomicClockCandidate256SecondPreserved =
  refl

canonicalAtomicClockCandidate256HertzPreserved :
  AtomicClockCandidate256DimensionAdapter.hertzDimensionPreserved
    canonicalAtomicClockCandidate256DimensionAdapter
  ≡
  refl
canonicalAtomicClockCandidate256HertzPreserved =
  refl

canonicalAtomicClockCandidate256RadPerSecondPreserved :
  AtomicClockCandidate256DimensionAdapter.radPerSecondDimensionPreserved
    canonicalAtomicClockCandidate256DimensionAdapter
  ≡
  refl
canonicalAtomicClockCandidate256RadPerSecondPreserved =
  refl

canonicalAtomicClockCandidate256CyclePreserved :
  AtomicClockCandidate256DimensionAdapter.cycleDimensionPreserved
    canonicalAtomicClockCandidate256DimensionAdapter
  ≡
  refl
canonicalAtomicClockCandidate256CyclePreserved =
  refl

canonicalAtomicClockCandidate256NoAuthorityTokenConstructedFalse :
  AtomicClockCandidate256DimensionAdapter.noAuthorityTokenConstructed
    canonicalAtomicClockCandidate256DimensionAdapter
  ≡
  false
canonicalAtomicClockCandidate256NoAuthorityTokenConstructedFalse =
  refl

canonicalAtomicClockCandidate256NoExternalReceiptConstructedFalse :
  AtomicClockCandidate256DimensionAdapter.noCandidate256ExternalReceiptConstructed
    canonicalAtomicClockCandidate256DimensionAdapter
  ≡
  false
canonicalAtomicClockCandidate256NoExternalReceiptConstructedFalse =
  refl

canonicalAtomicClockCandidate256NoPromotionFalse :
  AtomicClockCandidate256DimensionAdapter.noW4PhysicalCalibrationPromotion
    canonicalAtomicClockCandidate256DimensionAdapter
  ≡
  false
canonicalAtomicClockCandidate256NoPromotionFalse =
  refl
