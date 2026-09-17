module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSIQuantityBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Int using (negsuc)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Units.SI as SI
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseBEMetaAcquisitionExact as Protocol
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFigureFivePanelCFullNumericAcquisitionExact as Figure5
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr

------------------------------------------------------------------------
-- ADENYLATE-KINASE SI QUANTITY BRIDGE
--
-- This is an adapter, not a new unit ontology.  Source-side printed units are
-- retained and injected into the canonical DASHI.Physics.Units.SI carrier.
-- Unit conversion changes representation only: it does not pay a missing
-- measurement, observable identity, same-object weld, or scientific claim.
------------------------------------------------------------------------

siSourceDOI : String
siSourceDOI = SI.siSourceDOI

adkArticleDOI = Attr.articleDOI

angstromScale : SI.DecimalScale
angstromScale = SI.tenTo (negsuc 9)       -- 10^-10 metre

picosecondScale : SI.DecimalScale
picosecondScale = SI.tenTo (negsuc 11)    -- 10^-12 second

protocol : Protocol.BEMetaProtocol
protocol = Protocol.canonicalBEMetaProtocol

------------------------------------------------------------------------
-- Exact source-unit injections.
------------------------------------------------------------------------

dLnLowerSI : SI.Quantity SI.Length angstromScale
dLnLowerSI = SI.quantity false (Protocol.dLnLowerAngstrom protocol)

dLnUpperSI : SI.Quantity SI.Length angstromScale
dLnUpperSI = SI.quantity false (Protocol.dLnUpperAngstrom protocol)

dLnGaussianWidthSI : SI.Quantity SI.Length angstromScale
dLnGaussianWidthSI =
  -- The source stores tenths of an angstrom, so use one extra decimal digit.
  SI.quantity false (Protocol.dLnGaussianWidthTenthsAngstrom protocol * 1)

coordinateSaveTimeSI : SI.Quantity SI.Time picosecondScale
coordinateSaveTimeSI = SI.quantity false (Protocol.coordinateSavePicoseconds protocol)

gaussianDepositionTimeSI : SI.Quantity SI.Time picosecondScale
gaussianDepositionTimeSI = SI.quantity false (Protocol.gaussianDepositionPicoseconds protocol)

swapAttemptTimeSI : SI.Quantity SI.Time picosecondScale
swapAttemptTimeSI = SI.quantity false (Protocol.swapAttemptPicoseconds protocol)

replicaDurationSI : SI.Quantity SI.Time SI.nanoScale
replicaDurationSI = SI.quantity false (Protocol.nanosecondsPerReplica protocol)

totalBEMetaDurationSI : SI.Quantity SI.Time SI.nanoScale
totalBEMetaDurationSI = SI.quantity false (Protocol.totalNanosecondsPerBEMeta protocol)

temperatureSI : SI.Quantity SI.Temperature SI.unitScale
temperatureSI = SI.quantity false (Protocol.temperatureKelvin protocol)

pressureSI : SI.Quantity SI.Pressure SI.unitScale
pressureSI = SI.quantity false (Protocol.pressureBar protocol * 100000)

------------------------------------------------------------------------
-- Exact conventional energy/rate conversions into SI dimensions.
--
-- 1 thermochemical kcal = 4184 J.  The Figure-5 state energies are stored in
-- tenths of kcal mol^-1, so one stored unit = 418.4 J mol^-1 = 4184 deci-J/mol.
-- The BE-META Gaussian height is stored in hundredths of kcal mol^-1, so one
-- stored unit = 41.84 J mol^-1 = 4184 centi-J/mol.
------------------------------------------------------------------------

tenthsKcalMolToDeciJMol : Nat → SI.Quantity SI.MolarEnergy SI.deciScale
tenthsKcalMolToDeciJMol n = SI.quantity false (n * 4184)

hundredthsKcalMolToCentiJMol : Nat → SI.Quantity SI.MolarEnergy SI.centiScale
hundredthsKcalMolToCentiJMol n = SI.quantity false (n * 4184)

gaussianHeightSI : SI.Quantity SI.MolarEnergy SI.centiScale
gaussianHeightSI =
  hundredthsKcalMolToCentiJMol (Protocol.gaussianHeightHundredthsKcalMol protocol)

alphaRelativeEnergySI : SI.Quantity SI.MolarEnergy SI.deciScale
alphaRelativeEnergySI = tenthsKcalMolToDeciJMol (Figure5.tenthsKcalMol Figure5.alphaEnergy)

epsilonRelativeEnergySI : SI.Quantity SI.MolarEnergy SI.deciScale
epsilonRelativeEnergySI = tenthsKcalMolToDeciJMol (Figure5.tenthsKcalMol Figure5.epsilonEnergy)

-- Figure-5 stores n as hundredths of the printed unit 10^-2 ns^-1.
-- Therefore n -> n * 10^5 s^-1 exactly.
hundredthsDisplayRateToPerSecond : Nat → SI.Quantity SI.Frequency SI.unitScale
hundredthsDisplayRateToPerSecond n = SI.quantity false (n * 100000)

alphaToBetaRateSI : SI.Quantity SI.Frequency SI.unitScale
alphaToBetaRateSI =
  hundredthsDisplayRateToPerSecond (Figure5.hundredthsOfDisplayUnit Figure5.alphaToBeta)

-- Figure-5 reports D ~= 4.47e-3 rad^2/ns.  In SI the radian is dimensionless,
-- so the dimensional carrier is inverse time; 4.47e-3/ns = 4.47e6/s.
kramersAngularDiffusionSI : SI.Quantity SI.Frequency SI.unitScale
kramersAngularDiffusionSI = SI.quantity false 4470000

------------------------------------------------------------------------
-- Angle boundary.
--
-- The source theta coordinates are printed in degrees.  The current exact
-- fixed-point SI carrier has no exact algebraic representation of pi/180, so
-- this owner deliberately does not pretend to provide an exact degree->radian
-- numeral.  The angle observable definition remains source-owned and retained.
------------------------------------------------------------------------

thetaAngleSourceRole : String
thetaAngleSourceRole =
  "theta1/theta2 remain source-defined degree observables; radians are dimensionless in SI, but an exact fixed-point degree-to-radian numeral is not claimed"

------------------------------------------------------------------------
-- Attribution / WrongType firewalls.
------------------------------------------------------------------------

data UnitConversionCreatesScientificPayment : Set where
data TypedSIQuantityCreatesObservableIdentity : Set where
data TypedRateCreatesExperimentalKinetics : Set where
data TypedRelativeEnergyCreatesAbsoluteFreeEnergy : Set where

unitConversionDoesNotCreateScientificPayment : UnitConversionCreatesScientificPayment → ⊥
unitConversionDoesNotCreateScientificPayment ()

typedQuantityDoesNotCreateObservableIdentity : TypedSIQuantityCreatesObservableIdentity → ⊥
typedQuantityDoesNotCreateObservableIdentity ()

typedRateDoesNotBecomeExperimental : TypedRateCreatesExperimentalKinetics → ⊥
typedRateDoesNotBecomeExperimental ()

typedRelativeEnergyDoesNotBecomeAbsolute : TypedRelativeEnergyCreatesAbsoluteFreeEnergy → ⊥
typedRelativeEnergyDoesNotBecomeAbsolute ()

record AdKSIQuantityBridgeBoundary : Set where
  constructor adk-si-quantity-bridge-boundary
  field
    sourceDistancesInjectedIntoSILength : Bool
    sourceTimesInjectedIntoSITime : Bool
    sourcePressureInjectedIntoSIPressure : Bool
    sourceTemperatureInjectedIntoSITemperature : Bool
    relativeEnergyInjectedIntoSIMolarEnergy : Bool
    kramersDisplayRateInjectedIntoSIFrequency : Bool
    angularDiffusionUsesDimensionlessRadianSquared : Bool
    degreeToRadianExactFixedPointBridgeClaimed : Bool
    unitConversionCreatesScientificPayment : Bool
    identifierCreatesSIQuantityPayment : Bool
    typedKramersRateEqualsExperimentalRate : Bool
    typedRelativeEnergyEqualsAbsoluteThermodynamicFreeEnergy : Bool
open AdKSIQuantityBridgeBoundary public

canonicalAdKSIQuantityBridgeBoundary : AdKSIQuantityBridgeBoundary
canonicalAdKSIQuantityBridgeBoundary =
  adk-si-quantity-bridge-boundary
    true true true true true true true
    false false false false false
