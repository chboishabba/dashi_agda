module DASHI.Physics.Photovoltaic.PV369NetHalfThresholdExact where

-- PV first: real electrical >50% aperture solar input is a strict GATE.
-- Chemical products, heat, stored energy and gross photons cannot be
-- substituted for measured net electrical power.
--
-- Prior authors/owners reused:
--   PVPrimaryConversionMaxCutExact: source + driven-work + inventory ports
--   Circuit36927RecoveryEnergyBoundExact: Nat _≤_ proof skeleton
--   SolarOpticalSiteFibreCrossPollinationExact: same-asset/site spectrum
--   DriftDiffusionContinuityExact: collected-carrier physical consumer
-- This module does NOT assert any device passes the >50% gate.
-- Agda kernel acceptance remains OPEN.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound
import DASHI.Physics.Photovoltaic.PVPrimaryConversionMaxCutExact as PV
import DASHI.Physics.Semiconductor.Device.DriftDiffusionContinuityExact as Carrier
import DASHI.Environment.SolarOpticalSiteFibreCrossPollinationExact as Site

data False : Set where

-- The earlier MatchedDrivenPVGain field admitted ties. It is now a strict
-- successor inequality; this generic lemma proves ties cannot satisfy it.
successorNotLeItself : (n : Nat) -> Bound._≤_ (suc n) n -> False
successorNotLeItself zero ()
successorNotLeItself (suc n) (Bound.s≤s proof) =
  successorNotLeItself n proof

strictHalfExcludesTie :
  (net solar : Nat) ->
  solar ≡ net + net ->
  Bound._≤_ (suc solar) (net + net) ->
  False
strictHalfExcludesTie net .(net + net) refl proof =
  successorNotLeItself (net + net) proof

-- Use a common integer energy/power quantum integrated over the SAME
-- illuminated aperture and measurement window; no mixing a 665-sun DNI
-- numerator with one-sun AM1.5G denominator.
record NetSolarElectricPVAcceptance : Set where
  field
    measuredIncidentApertureSolar : Nat
    measuredGrossElectric : Nat
    measuredDriverElectricIn : Nat
    measuredDriverElectricRecovered : Nat
    measuredAuxiliaryElectricDraw : Nat
    measuredNetElectricExport : Nat

    sameTimeAndApertureSource : String
    tracedASTMG173OrObservedSpectrum : String
    calibratedSourceAndElectricalMeters : String
    independentlyVerifiedDevicePCE : String

    -- Explicit signed electric port conservation. No thermal or chemical
    -- coproduct is counted as electric export.
    netElectricPortIdentity :
      measuredGrossElectric + measuredDriverElectricRecovered
      ≡ measuredNetElectricExport +
        (measuredDriverElectricIn + measuredAuxiliaryElectricDraw)

    -- Strict >50%, not >=50; no rounded percentage accepts equality.
    strictlyAboveHalfSolar :
      Bound._≤_ (suc measuredIncidentApertureSolar)
        (measuredNetElectricExport + measuredNetElectricExport)

-- The original 2026 ideal three-junction MODEL at 51.741%, 2-terminal,
-- corresponds to 51,741 in 100,000 fractional power units. It is not a
-- witness of this experiment/source-specific acceptance record.
modelThreeJunctionPercentUnits modelHalfPercentUnits : Nat
modelThreeJunctionPercentUnits = 51741
modelHalfPercentUnits = 50000

idealThreeJunctionHeadroomUnits : Nat
idealThreeJunctionHeadroomUnits = 1741

idealModelHeadroomArithmetic :
  modelHalfPercentUnits + idealThreeJunctionHeadroomUnits
  ≡ modelThreeJunctionPercentUnits
idealModelHeadroomArithmetic = refl

-- This is only 1741/51741 ≈ 3.36% of ideal electric output available
-- for all combined losses before slipping to <=50%. No actual 3J
-- architecture is shown to attain the ideal or stay inside that budget.
record ThreeJunctionRealLossCertificate : Set₁ where
  field
    sameApertureAndSpectrum : Set
    sourceApertureProof : sameApertureAndSpectrum

    actualThreeJunctionStack : Set
    sourceStack : actualThreeJunctionStack

    measuredMultijunctionCurrentMatching : Set
    measuredCurrentMatch : measuredMultijunctionCurrentMatching

    measuredContactEscapeThermalLosses : Set
    lossReceipt : measuredContactEscapeThermalLosses

    sourceSolarNetPCE : NetSolarElectricPVAcceptance

-- P3 drive, P4 multiplication, P5 optical film and P6 bio outputs remain
-- independent paths with separate energy and work ledgers.
