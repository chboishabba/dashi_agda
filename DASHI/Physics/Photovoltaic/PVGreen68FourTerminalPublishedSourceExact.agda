module DASHI.Physics.Photovoltaic.PVGreen68FourTerminalPublishedSourceExact where

-- M2 source-grounded one-sun 4-terminal conventional control.
-- 2026 Green et al., Solar Cell Efficiency Tables v68, Joule
-- DOI 10.1016/j.joule.2026.102494, Table 4, NREL 02/2017.
-- Mechanical GaInP/GaAs//Si four-terminal independent contact groups:
-- Voc 2.52 / 0.681 V, Jsc 13.6 / 11.0 mA cm-2,
-- FF 87.5 / 78.5 percent, reported total 35.9 +/-0.5%.
--
-- Nat source values are in units one-millionth of a PERCENTAGE POINT:
-- top: 29.988000%, Si: 5.880435%, sum 35.868435%.
-- The 0.031565 pp difference to printed 35.9 is numerical reporting;
-- it is NOT a new uncertainty, accepted device source, or 369 claim.
-- No original per-channel IV raw files or independent authentic instrument
-- interval are supplied. This file only proves the source arithmetic.
-- Golden Agda check OPEN; no ESD edits.

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound
import DASHI.Physics.Photovoltaic.PV369NetHalfThresholdExact as Net
import DASHI.Physics.Photovoltaic.PV369FourJunctionOpticsToMeasuredIVExact as P5

topGroupPublishedPowerUnits siliconGroupPublishedPowerUnits : Nat
topGroupPublishedPowerUnits = 29988000
siliconGroupPublishedPowerUnits = 5880435

summedPublishedFourTerminalUnits reportedRoundedFourTerminalUnits : Nat
summedPublishedFourTerminalUnits = 35868435
reportedRoundedFourTerminalUnits = 35900000

sourceFourTerminalSumIdentity :
  topGroupPublishedPowerUnits + siliconGroupPublishedPowerUnits
  ≡ summedPublishedFourTerminalUnits
sourceFourTerminalSumIdentity = refl

sourcePrintedDifference :
  summedPublishedFourTerminalUnits + 31565
  ≡ reportedRoundedFourTerminalUnits
sourcePrintedDifference = refl

oneSunHalfSourceUnits : Nat
oneSunHalfSourceUnits = 50000000

-- Exact same-unit source headroom, proven by builtin Nat normalization:
-- 35.900000% + 14.100000 percentage points = 50.000000%.
sourceFourTerminalHeadroomExact :
  reportedRoundedFourTerminalUnits + 14100000 ≡ oneSunHalfSourceUnits
sourceFourTerminalHeadroomExact = refl

-- For an inductive order witness, rescale *only the reported one-decimal*
-- claim onto a separate 0.1 percentage-point grid: 359 < 500.
-- This avoids an impractical 35,900,000-deep unary order construction.
reportedOneDecimalUnits halfOneDecimalUnits : Nat
reportedOneDecimalUnits = 359
halfOneDecimalUnits = 500

reportedOneDecimalHeadroom :
  reportedOneDecimalUnits + 141 ≡ halfOneDecimalUnits
reportedOneDecimalHeadroom = refl

-- Strictly below half in the explicitly coarse published-value grid.
-- This says NOTHING about a proposed 369 device or ideal model.
sourceFourTerminalReportedBelowHalf :
  Bound._≤_ reportedOneDecimalUnits halfOneDecimalUnits
sourceFourTerminalReportedBelowHalf =
  Bound.≤-append reportedOneDecimalUnits 141

-- A 2T V*J*FF identity would miss independently contacted groups;
-- the source aggregation assumes shared normalized illumination area.
-- Source calibration, same optical material, and true 369 operator remain
-- separate uninhabited physical admission obligations.
record SourceMeasuredNREL2017FourTerminalAdmission : Set₁ where
  field
    OriginalMeasuredIVGroups : Set
    sourceIV : OriginalMeasuredIVGroups
    SamePhysicalAperture : Set
    sourceAperture : SamePhysicalAperture
    OriginalIrradianceAndSpectrum : Set
    sourceIllumination : OriginalIrradianceAndSpectrum
    IndependentStabilizedMPP : Set
    trueStabilizedMPP : IndependentStabilizedMPP
    InstrumentAndUncertaintyReceipts : Set
    calibratedMetrology : InstrumentAndUncertaintyReceipts
