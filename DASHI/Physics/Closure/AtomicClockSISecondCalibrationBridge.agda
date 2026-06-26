module DASHI.Physics.Closure.AtomicClockSISecondCalibrationBridge where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.ChemistryPhysicalHandoffDiagnostic as Handoff
import DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation as External
import DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptRequestPack as Request
import DASHI.Physics.Closure.W4PhysicalCalibrationProviderAttempt as Provider
import DASHI.Physics.Closure.W4StrictPhysicalNextObligation as Next
import DASHI.Physics.Closure.W4SurrogateScaleSettingBoundary as Surrogate

------------------------------------------------------------------------
-- Atomic-clock / SI-second calibration bridge.
--
-- This module records the exact SI time/frequency shape needed by the W4
-- physical-calibration request without constructing the external
-- Candidate256 authority token.  It is a typed bridge/request surface: the
-- SI second and hertz dimensions are present, the Cs-133 integer anchor is
-- present, and the existing W4 provider attempt remains the source of truth
-- for why no Candidate256PhysicalCalibrationExternalReceipt or W4 promotion
-- is locally available.

data SITimeFrequencyUnit : Set where
  second :
    SITimeFrequencyUnit

  hertz :
    SITimeFrequencyUnit

  radPerSecond :
    SITimeFrequencyUnit

  cycle :
    SITimeFrequencyUnit

record SIExponent : Set where
  field
    positive :
      Nat

    negative :
      Nat

open SIExponent public

zeroExponent : SIExponent
zeroExponent =
  record
    { positive = zero
    ; negative = zero
    }

positiveOneExponent : SIExponent
positiveOneExponent =
  record
    { positive = suc zero
    ; negative = zero
    }

negativeOneExponent : SIExponent
negativeOneExponent =
  record
    { positive = zero
    ; negative = suc zero
    }

record SIBaseDimensionVector : Set where
  field
    length :
      SIExponent

    mass :
      SIExponent

    time :
      SIExponent

    current :
      SIExponent

    temperature :
      SIExponent

    amount :
      SIExponent

    luminousIntensity :
      SIExponent

open SIBaseDimensionVector public

dimensionlessVector : SIBaseDimensionVector
dimensionlessVector =
  record
    { length = zeroExponent
    ; mass = zeroExponent
    ; time = zeroExponent
    ; current = zeroExponent
    ; temperature = zeroExponent
    ; amount = zeroExponent
    ; luminousIntensity = zeroExponent
    }

siSecondDimension : SIBaseDimensionVector
siSecondDimension =
  record
    { length = zeroExponent
    ; mass = zeroExponent
    ; time = positiveOneExponent
    ; current = zeroExponent
    ; temperature = zeroExponent
    ; amount = zeroExponent
    ; luminousIntensity = zeroExponent
    }

siHertzDimension : SIBaseDimensionVector
siHertzDimension =
  record
    { length = zeroExponent
    ; mass = zeroExponent
    ; time = negativeOneExponent
    ; current = zeroExponent
    ; temperature = zeroExponent
    ; amount = zeroExponent
    ; luminousIntensity = zeroExponent
    }

siRadPerSecondDimension : SIBaseDimensionVector
siRadPerSecondDimension =
  siHertzDimension

siCycleDimension : SIBaseDimensionVector
siCycleDimension =
  dimensionlessVector

siUnitDimension :
  SITimeFrequencyUnit →
  SIBaseDimensionVector
siUnitDimension second =
  siSecondDimension
siUnitDimension hertz =
  siHertzDimension
siUnitDimension radPerSecond =
  siRadPerSecondDimension
siUnitDimension cycle =
  siCycleDimension

cs133ExactInteger : Nat
cs133ExactInteger =
  9192631770

deltaNuCsName : String
deltaNuCsName =
  "Delta nu Cs"

oneSecondCs133PeriodsStatement : String
oneSecondCs133PeriodsStatement =
  "1 second = 9192631770 periods"

record Cs133SISecondAnchor : Set where
  field
    exactInteger :
      Nat

    transitionName :
      String

    periodStatement :
      String

    timeUnit :
      SITimeFrequencyUnit

    frequencyUnit :
      SITimeFrequencyUnit

    periodCountUnit :
      SITimeFrequencyUnit

    timeDimension :
      SIBaseDimensionVector

    frequencyDimension :
      SIBaseDimensionVector

    exactIntegerIsCs133 :
      exactInteger ≡ cs133ExactInteger

open Cs133SISecondAnchor public

canonicalCs133SISecondAnchor : Cs133SISecondAnchor
canonicalCs133SISecondAnchor =
  record
    { exactInteger = cs133ExactInteger
    ; transitionName = deltaNuCsName
    ; periodStatement = oneSecondCs133PeriodsStatement
    ; timeUnit = second
    ; frequencyUnit = hertz
    ; periodCountUnit = cycle
    ; timeDimension = siSecondDimension
    ; frequencyDimension = siHertzDimension
    ; exactIntegerIsCs133 = refl
    }

natToSISecondCalibrationRoute :
  Nat →
  SITimeFrequencyUnit
natToSISecondCalibrationRoute _ =
  second

candidate256QuotientToSISecondRoute :
  Surrogate.Candidate256QuotientClass →
  SITimeFrequencyUnit
candidate256QuotientToSISecondRoute _ =
  second

candidate256SISecondRouteFactorsThroughNat :
  (q : Surrogate.Candidate256QuotientClass) →
  candidate256QuotientToSISecondRoute q
  ≡
  natToSISecondCalibrationRoute (Surrogate.candidate256SurrogateScale q)
candidate256SISecondRouteFactorsThroughNat _ =
  refl

SISecondDimensionalPreservationRequest :
  Handoff.QuotientLawAtWitness Next.canonicalCandidate256QuotientLaw →
  Set
SISecondDimensionalPreservationRequest _ =
  siUnitDimension second ≡ siSecondDimension

siSecondDimensionalPreservationRequested :
  (law : Handoff.QuotientLawAtWitness Next.canonicalCandidate256QuotientLaw) →
  SISecondDimensionalPreservationRequest law
siSecondDimensionalPreservationRequested _ =
  refl

record AtomicClockSISecondCalibrationBridge : Setω where
  field
    cs133Anchor :
      Cs133SISecondAnchor

    physicalUnitCarrier :
      Set

    physicalUnitCarrierAvailable :
      Bool

    physicalUnitCarrierIsSITimeFrequencyUnit :
      physicalUnitCarrier ≡ SITimeFrequencyUnit

    secondDimension :
      SIBaseDimensionVector

    hertzDimension :
      SIBaseDimensionVector

    radPerSecondDimension :
      SIBaseDimensionVector

    cycleDimension :
      SIBaseDimensionVector

    natToUnitCalibrationRoute :
      Nat →
      physicalUnitCarrier

    quotientScaleRoute :
      Surrogate.Candidate256QuotientClass →
      physicalUnitCarrier

    factorizationLawRequest :
      (q : Surrogate.Candidate256QuotientClass) →
      quotientScaleRoute q
      ≡
      natToUnitCalibrationRoute (Surrogate.candidate256SurrogateScale q)

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

    w4BlockedFields :
      List External.Candidate256PhysicalCalibrationExternalBlockedField

    w4NonPromotionBoundary :
      List String

    noLocalAuthorityTokenGuard :
      Bool

    noCandidate256ExternalReceiptGuard :
      Bool

    noW4PromotionGuard :
      Bool

    noLocalAuthorityTokenGuardIsFalse :
      noLocalAuthorityTokenGuard ≡ false

    noCandidate256ExternalReceiptGuardIsFalse :
      noCandidate256ExternalReceiptGuard ≡ false

    noW4PromotionGuardIsFalse :
      noW4PromotionGuard ≡ false

    bridgeBoundary :
      List String

open AtomicClockSISecondCalibrationBridge public

canonicalAtomicClockSISecondCalibrationBridge :
  AtomicClockSISecondCalibrationBridge
canonicalAtomicClockSISecondCalibrationBridge =
  record
    { cs133Anchor =
        canonicalCs133SISecondAnchor
    ; physicalUnitCarrier =
        SITimeFrequencyUnit
    ; physicalUnitCarrierAvailable =
        true
    ; physicalUnitCarrierIsSITimeFrequencyUnit =
        refl
    ; secondDimension =
        siSecondDimension
    ; hertzDimension =
        siHertzDimension
    ; radPerSecondDimension =
        siRadPerSecondDimension
    ; cycleDimension =
        siCycleDimension
    ; natToUnitCalibrationRoute =
        natToSISecondCalibrationRoute
    ; quotientScaleRoute =
        candidate256QuotientToSISecondRoute
    ; factorizationLawRequest =
        candidate256SISecondRouteFactorsThroughNat
    ; dimensionalPreservationRequest =
        SISecondDimensionalPreservationRequest
    ; dimensionalPreservationRequested =
        siSecondDimensionalPreservationRequested
    ; w4ProviderAttempt =
        Provider.canonicalW4PhysicalCalibrationProviderAttempt
    ; w4RequestPack =
        Request.canonicalW4PhysicalCalibrationExternalReceiptRequestPack
    ; w4ExternalStatus =
        External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; w4BlockedFields =
        External.canonicalCandidate256PhysicalCalibrationExternalBlockedFields
    ; w4NonPromotionBoundary =
        External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus.noPromotionBoundary
          External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; noLocalAuthorityTokenGuard =
        false
    ; noCandidate256ExternalReceiptGuard =
        false
    ; noW4PromotionGuard =
        false
    ; noLocalAuthorityTokenGuardIsFalse =
        refl
    ; noCandidate256ExternalReceiptGuardIsFalse =
        refl
    ; noW4PromotionGuardIsFalse =
        refl
    ; bridgeBoundary =
        "SI time/frequency carrier is available as a local unit-shape datatype"
        ∷ "Cs-133 exact integer 9192631770 is recorded for Delta nu Cs"
        ∷ "The bridge records 1 second = 9192631770 periods as a local SI anchor string"
        ∷ "No Candidate256PhysicalCalibrationAuthorityToken is constructed here"
        ∷ "No Candidate256PhysicalCalibrationExternalReceipt is constructed here"
        ∷ "No W4 physical-calibration promotion is claimed here"
        ∷ []
    }

canonicalAtomicClockPhysicalUnitCarrierAvailable :
  AtomicClockSISecondCalibrationBridge.physicalUnitCarrierAvailable
    canonicalAtomicClockSISecondCalibrationBridge
  ≡
  true
canonicalAtomicClockPhysicalUnitCarrierAvailable =
  refl

canonicalAtomicClockPhysicalUnitCarrierIsSITimeFrequencyUnit :
  AtomicClockSISecondCalibrationBridge.physicalUnitCarrier
    canonicalAtomicClockSISecondCalibrationBridge
  ≡
  SITimeFrequencyUnit
canonicalAtomicClockPhysicalUnitCarrierIsSITimeFrequencyUnit =
  refl

canonicalAtomicClockNoLocalAuthorityTokenGuardFalse :
  AtomicClockSISecondCalibrationBridge.noLocalAuthorityTokenGuard
    canonicalAtomicClockSISecondCalibrationBridge
  ≡
  false
canonicalAtomicClockNoLocalAuthorityTokenGuardFalse =
  refl

canonicalAtomicClockNoCandidate256ExternalReceiptGuardFalse :
  AtomicClockSISecondCalibrationBridge.noCandidate256ExternalReceiptGuard
    canonicalAtomicClockSISecondCalibrationBridge
  ≡
  false
canonicalAtomicClockNoCandidate256ExternalReceiptGuardFalse =
  refl

canonicalAtomicClockNoW4PromotionGuardFalse :
  AtomicClockSISecondCalibrationBridge.noW4PromotionGuard
    canonicalAtomicClockSISecondCalibrationBridge
  ≡
  false
canonicalAtomicClockNoW4PromotionGuardFalse =
  refl

canonicalAtomicClockCs133IntegerExact :
  Cs133SISecondAnchor.exactInteger
    (AtomicClockSISecondCalibrationBridge.cs133Anchor
      canonicalAtomicClockSISecondCalibrationBridge)
  ≡
  cs133ExactInteger
canonicalAtomicClockCs133IntegerExact =
  refl

canonicalAtomicClockFactorizationRequested :
  (q : Surrogate.Candidate256QuotientClass) →
  AtomicClockSISecondCalibrationBridge.quotientScaleRoute
    canonicalAtomicClockSISecondCalibrationBridge
    q
  ≡
  AtomicClockSISecondCalibrationBridge.natToUnitCalibrationRoute
    canonicalAtomicClockSISecondCalibrationBridge
    (Surrogate.candidate256SurrogateScale q)
canonicalAtomicClockFactorizationRequested =
  AtomicClockSISecondCalibrationBridge.factorizationLawRequest
    canonicalAtomicClockSISecondCalibrationBridge
