module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSIQuantityBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Int using (negsuc)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Physics.Units.SI as SI
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseBEMetaAcquisitionExact as BEMeta
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseRateObserverAdequacyExact as Rate
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr

------------------------------------------------------------------------
-- TYPED SI BRIDGE FOR ADK SOURCE QUANTITIES
--
-- BIPM owns SI dimensions/units; Li-Liu-Ji owns the source-side AdK values.
-- DASHI owns these exact unit conversions and the weld between the two carriers.
-- A conversion does not create a new empirical measurement or improve source
-- precision.
------------------------------------------------------------------------

siSourceDOI : String
siSourceDOI = SI.siSourceDOI

bipmSource : Attribution.AttributedSource
bipmSource = Attribution.mkDOISource
  "Bureau International des Poids et Mesures"
  "The International System of Units (SI), 9th edition, revision 4.01"
  "BIPM"
  "2026"
  "10.59161/AUEZ1291"
  "https://www.bipm.org/en/publications/si-brochure"
  Attribution.technicalStandardSource
  "pays SI unit and dimension semantics only; DASHI owns the typed conversion fixtures"
  Attribution.publicAttribution

bipmReceipt : Snowball.SourceRoleSnowballReceipt bipmSource
bipmReceipt = Snowball.canonicalSourceRoleSnowballReceipt bipmSource

adkSource : Attribution.AttributedSource
adkSource = Attr.liLiuJiSource

------------------------------------------------------------------------
-- Exact decimal scales and typed quantities.
------------------------------------------------------------------------

angstromScale : SI.DecimalScale
angstromScale = SI.tenTo (negsuc 9)      -- 10^-10 m

nanosecondScale : SI.DecimalScale
nanosecondScale = SI.tenTo (negsuc 8)    -- 10^-9 s

picosecondScale : SI.DecimalScale
picosecondScale = SI.tenTo (negsuc 11)   -- 10^-12 s

tenthScale : SI.DecimalScale
tenthScale = SI.tenTo (negsuc 0)         -- 10^-1

angstromLength : SI.Quantity SI.Length angstromScale
angstromLength = SI.posQ 1

nanosecondTime : SI.Quantity SI.Time nanosecondScale
nanosecondTime = SI.posQ 1

picosecondTime : SI.Quantity SI.Time picosecondScale
picosecondTime = SI.posQ 1

oneBarPressure : SI.Quantity SI.Pressure SI.unitScale
oneBarPressure = SI.posQ 100000

threeHundredKelvin : SI.Quantity SI.Temperature SI.unitScale
threeHundredKelvin = SI.posQ 300

-- 0.1 kcal mol^-1 = 418.4 J mol^-1 = 4184 × 10^-1 J mol^-1.
oneTenthKcalPerMolSI : SI.Quantity SI.MolarEnergy tenthScale
oneTenthKcalPerMolSI = SI.posQ 4184

-- 10^-2 ns^-1 = 10^7 s^-1.  Radian is dimensionless in SI, therefore the
-- Kramers angular-diffusion coordinate rad^2/ns has the Frequency dimension.
kramersRateUnitSI : SI.Quantity SI.Frequency SI.unitScale
kramersRateUnitSI = SI.posQ 10000000

apoAngularDiffusionSI : SI.Quantity SI.Frequency SI.unitScale
apoAngularDiffusionSI = SI.posQ 4470000

boundAngularDiffusionSI : SI.Quantity SI.Frequency SI.unitScale
boundAngularDiffusionSI = SI.posQ 513000

------------------------------------------------------------------------
-- Source weld receipts retain both source roles.
------------------------------------------------------------------------

record SIConversionReceipt : Set where
  constructor si-conversion-receipt
  field
    sourceQuantity : String
    sourceUnit : String
    targetDimension : SI.Dimension
    targetUnit : String
    exactScaleReading : String
    empiricalSource : Attribution.AttributedSource
    unitStandardSource : Attribution.AttributedSource
    conversionIsDASHISynthesis : Bool
    createsNewMeasurement : Bool
open SIConversionReceipt public

angstromReceipt : SIConversionReceipt
angstromReceipt = si-conversion-receipt
  "AdK geometric/CV distance"
  "angstrom"
  SI.Length
  "metre"
  "1 A = 10^-10 m"
  adkSource bipmSource true false

nanosecondReceipt : SIConversionReceipt
nanosecondReceipt = si-conversion-receipt
  "AdK simulation time"
  "ns"
  SI.Time
  "second"
  "1 ns = 10^-9 s"
  adkSource bipmSource true false

molarEnergyReceipt : SIConversionReceipt
molarEnergyReceipt = si-conversion-receipt
  "AdK relative free energy / bias height"
  "kcal mol^-1"
  SI.MolarEnergy
  "J mol^-1"
  "1 kcal mol^-1 = 4184 J mol^-1"
  adkSource bipmSource true false

kramersRateReceipt : SIConversionReceipt
kramersRateReceipt = si-conversion-receipt
  "Figure-5/6 Kramers edge-rate unit"
  "10^-2 ns^-1"
  SI.Frequency
  "s^-1"
  "10^-2 ns^-1 = 10^7 s^-1"
  adkSource bipmSource true false

bemetaProtocol : BEMeta.BEMetaProtocol
bemetaProtocol = BEMeta.canonicalBEMetaProtocol

apoKramersSource : Rate.KramersCalibration
apoKramersSource = Rate.apoKramersCalibration

boundKramersSource : Rate.KramersCalibration
boundKramersSource = Rate.boundKramersCalibration

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data SIConversionCreatesExperimentalMeasurement : Set where
data AngularDiffusionIsTranslationalDiffusion : Set where
data KramersRateUnitCreatesEdgeNumeral : Set where
data DimensionallyTypedMeansPhysicallyComplete : Set where

siConversionDoesNotCreateMeasurement : SIConversionCreatesExperimentalMeasurement → ⊥
siConversionDoesNotCreateMeasurement ()

angularDiffusionDoesNotBecomeTranslational : AngularDiffusionIsTranslationalDiffusion → ⊥
angularDiffusionDoesNotBecomeTranslational ()

rateUnitDoesNotCreateEdgeNumeral : KramersRateUnitCreatesEdgeNumeral → ⊥
rateUnitDoesNotCreateEdgeNumeral ()

dimensionalTypingDoesNotCreatePhysicalCompleteness : DimensionallyTypedMeansPhysicallyComplete → ⊥
dimensionalTypingDoesNotCreatePhysicalCompleteness ()

record AdKSIQuantityBridgeBoundary : Set where
  constructor adk-si-quantity-bridge-boundary
  field
    lengthDimensionTyped : Bool
    timeDimensionTyped : Bool
    pressureDimensionTyped : Bool
    temperatureDimensionTyped : Bool
    molarEnergyDimensionTyped : Bool
    kramersRateDimensionTyped : Bool
    angularDiffusionDimensionTypedAsInverseTime : Bool
    bipmDoiRetained : Bool
    liLiuJiAttributionRetained : Bool
    conversionCreatesNewMeasurement : Bool
    rateUnitCreatesMissingEdgeNumeral : Bool
    siTypingCreatesAtomisticDynamics : Bool

canonicalAdKSIQuantityBridgeBoundary : AdKSIQuantityBridgeBoundary
canonicalAdKSIQuantityBridgeBoundary = adk-si-quantity-bridge-boundary
  true true true true true true true true true false false false
