module DASHI.Physics.Motors.Resonate369DerivedFiniteGeometryExact where

------------------------------------------------------------------------
-- DERIVED GEOMETRY ONLY. No vendor CAD, STL, STEP, mesh or firmware.
--
-- Sources to inspect independently, without importing their assets:
-- David Holmstrom / Resonate369, Friendbeacon ISAV C07 hand-start
-- prototype, Dodecatron single-phase generator, impulse resonator.
-- Historical Infinity SAV 250-coil / 250-magnet presentation is a
-- separate attributed claim and is NOT identified with Holmstrom CAD.
--
-- This module certifies only discrete indexing and exact angular
-- arithmetic. It does not certify dimensions, mechanical safety,
-- magnet polarity, measured coil geometry, flux, power or over-unity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_; _+_)
open import Agda.Builtin.String using (String)

-- Millidegrees avoid imprecise floating point pitches, including 1.44°.
fullTurnMilliDegrees : Nat
fullTurnMilliDegrees = 360000

c07StationCount : Nat
c07StationCount = 8

dodecatronStationCount : Nat
dodecatronStationCount = 12

historicalMG10ClaimedStationCount : Nat
historicalMG10ClaimedStationCount = 250

c07NominalPitchMilliDegrees : Nat
c07NominalPitchMilliDegrees = 45000

dodecatronNominalPitchMilliDegrees : Nat
dodecatronNominalPitchMilliDegrees = 30000

historicalMG10ClaimedPitchMilliDegrees : Nat
historicalMG10ClaimedPitchMilliDegrees = 1440

-- All three counts have an exact whole-turn nominal pitch.
c07NominalPitchCloses :
  c07StationCount * c07NominalPitchMilliDegrees
  ≡ fullTurnMilliDegrees
c07NominalPitchCloses = refl

dodecatronNominalPitchCloses :
  dodecatronStationCount * dodecatronNominalPitchMilliDegrees
  ≡ fullTurnMilliDegrees
dodecatronNominalPitchCloses = refl

historicalMG10ClaimedPitchCloses :
  historicalMG10ClaimedStationCount *
  historicalMG10ClaimedPitchMilliDegrees
  ≡ fullTurnMilliDegrees
historicalMG10ClaimedPitchCloses = refl

-- A declarative witness that makes source-dependent station geometry
-- an explicit input rather than covertly assuming uniform placement.
-- 'angleMilliDegrees' can be derived from read-only CAD measurement;
-- it is intentionally NOT filled in using screenshots or guessed offsets.
record DerivedStationGeometry : Set where
  constructor derivedStationGeometry
  field
    stationCount : Nat
    angleMilliDegrees : Nat → Nat
    radialCoordinateMicrometres : Nat → Nat
    axialCoordinateMicrometres : Nat → Nat
    magneticAxisMilliDegrees : Nat → Nat
    coilAxisMilliDegrees : Nat → Nat
    polarityNorth : Nat → Bool
    clockwiseWinding : Nat → Bool
    sourceLabel : String

-- Known descriptive counts are separated from observed coordinates.
record GeometryReference : Set where
  constructor geometryReference
  field
    source : String
    claimedStations : Nat
    nominalPitchMilliDegrees : Nat
    nominalPitchCloses : claimedStations * nominalPitchMilliDegrees
                         ≡ fullTurnMilliDegrees
    actualCoordinatesMeasured : Bool
    sourceCADVendored : Bool
    sourceCADNotVendored : sourceCADVendored ≡ false

c07Reference : GeometryReference
c07Reference =
  geometryReference
    "Holmstrom / Resonate369 C07: claimed eight-position geometry"
    c07StationCount c07NominalPitchMilliDegrees
    c07NominalPitchCloses false false refl

dodecatronReference : GeometryReference
dodecatronReference =
  geometryReference
    "Holmstrom / Resonate369 Dodecatron: claimed 12 and 12"
    dodecatronStationCount dodecatronNominalPitchMilliDegrees
    dodecatronNominalPitchCloses false false refl

historicalMG10Reference : GeometryReference
historicalMG10Reference =
  geometryReference
    "Historical Infinity SAV presentation: claimed 250 coils and magnets"
    historicalMG10ClaimedStationCount historicalMG10ClaimedPitchMilliDegrees
    historicalMG10ClaimedPitchCloses false false refl

-- Nominal half-turn is an exact integer multiple for each geometry.
c07HalfTurn : 4 * c07NominalPitchMilliDegrees ≡ 180000
c07HalfTurn = refl

dodecatronHalfTurn : 6 * dodecatronNominalPitchMilliDegrees ≡ 180000
dodecatronHalfTurn = refl

historicalMG10HalfTurn :
  125 * historicalMG10ClaimedPitchMilliDegrees ≡ 180000
historicalMG10HalfTurn = refl

-- A further modelling layer may add cyclic Fin n indices,
-- physically measured nonuniform offsets, signed angle differences,
-- electromagnetic co-energy, and time-resolved power measurements.
-- None is silently admitted here.
