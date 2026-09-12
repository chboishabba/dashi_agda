module DASHI.Physics.Nuclear.LeBlancFSPICNumericEnvelopeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- SOURCE-EXACT FINITE ARITHMETIC FOR NASA NTRS 20250008475
--
-- The source exposes a closed in-core pressure range 900-1500 kPa and a mass-
-- flow range 0.05-0.5 kg/s.  Flow is encoded in hundredths of kg/s so both
-- endpoints are exact naturals.  Temperature and radiation values are kept as
-- one-sided / point-like notional coordinates rather than falsely converted to
-- closed intervals.
------------------------------------------------------------------------

pressureLowerKPa : Nat
pressureLowerKPa = 900

pressureUpperKPa : Nat
pressureUpperKPa = 1500

pressureSpanKPa : Nat
pressureSpanKPa = 600

pressureSpanCloses : pressureLowerKPa + pressureSpanKPa ≡ pressureUpperKPa
pressureSpanCloses = refl

massFlowLowerHundredthsKgPerS : Nat
massFlowLowerHundredthsKgPerS = 5

massFlowUpperHundredthsKgPerS : Nat
massFlowUpperHundredthsKgPerS = 50

massFlowSpanHundredths : Nat
massFlowSpanHundredths = 45

massFlowSpanCloses :
  massFlowLowerHundredthsKgPerS + massFlowSpanHundredths
  ≡ massFlowUpperHundredthsKgPerS
massFlowSpanCloses = refl

inCoreTemperatureThresholdK : Nat
inCoreTemperatureThresholdK = 1200

neutronFluxPowerOfTen : Nat
neutronFluxPowerOfTen = 12

neutronFluencePowerOfTen : Nat
neutronFluencePowerOfTen = 21

gammaDoseMantissa : Nat
gammaDoseMantissa = 8

gammaDosePowerOfTen : Nat
gammaDosePowerOfTen = 10

temperatureIsOneSidedThreshold : Bool
temperatureIsOneSidedThreshold = true

radiationCoordinatesAreNotClosedRanges : Bool
radiationCoordinatesAreNotClosedRanges = true

record FSPNumericEnvelopeWitness : Set where
  constructor fsp-numeric-envelope-witness
  field
    pressureLowKPa pressureHighKPa : Nat
    flowLowHundredths flowHighHundredths : Nat
    temperatureThresholdK : Nat
    neutronFluxExponent neutronFluenceExponent : Nat
    gammaMantissa gammaExponent : Nat

sourceNumericEnvelope : FSPNumericEnvelopeWitness
sourceNumericEnvelope = fsp-numeric-envelope-witness
  pressureLowerKPa pressureUpperKPa
  massFlowLowerHundredthsKgPerS massFlowUpperHundredthsKgPerS
  inCoreTemperatureThresholdK
  neutronFluxPowerOfTen neutronFluencePowerOfTen
  gammaDoseMantissa gammaDosePowerOfTen

notionalEnvelopeDoesNotPayQualification : Bool
notionalEnvelopeDoesNotPayQualification = false

numericEnvelopeDoesNotSelectUniqueSensor : Bool
numericEnvelopeDoesNotSelectUniqueSensor = false

numericEnvelopeDoesNotPayMissionUniversalRequirement : Bool
numericEnvelopeDoesNotPayMissionUniversalRequirement = false
