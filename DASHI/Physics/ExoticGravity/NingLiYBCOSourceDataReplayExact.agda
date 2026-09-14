module DASHI.Physics.ExoticGravity.NingLiYBCOSourceDataReplayExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.NingLiYBCOGravityConstraintBidiExact as Static
import DASHI.Physics.ExoticGravity.NingLiYBCORotatingFieldConstraintExact as Rotating

------------------------------------------------------------------------
-- NING LI / YBCO SOURCE-DATA REPLAY
--
-- Source-exact public coordinates from Physica C 281 (1997) 260-267,
-- DOI 10.1016/S0921-4534(97)01462-7, and NASA NTRS 19990019627.
-- This is a finite comparison of two published test regimes.  It does not
-- identify later AC Gravity / Army apparatus as the same object.
------------------------------------------------------------------------

record NingSourceDataReplay : Set where
  constructor ning-source-data-replay
  field
    staticSource : String
    staticMaterial : String
    staticDrive : String
    staticAccelerationBoundPartsPerHundredMillionG : Nat
    rotatingSource : String
    rotatingDiskDiameterCm : Nat
    rotatingFieldRateRPM : Nat
    outerFieldUpperGauss : Nat
    centreFieldUpperGauss : Nat
    dcLevitationVariantsPresent : Bool
    positiveStaticEffectObserved : Bool
    positiveRotatingEffectObserved : Bool
    sameApparatusObjectPaid : Bool
    laterArmyContinuityPaid : Bool

open NingSourceDataReplay public

ningSourceDataReplay : NingSourceDataReplay
ningSourceDataReplay = ning-source-data-replay
  "Physica C 281 (1997) 260-267; DOI 10.1016/S0921-4534(97)01462-7; NASA NTRS 19990039542"
  "bulk type-II YBCO superconductor"
  "stable levitation in a DC magnetic field; sensitive gravimeter"
  2
  "NASA NTRS 19990019627; AIAA-98-3139"
  15
  12000
  60
  10
  true
  false
  false
  false
  false

existingStaticReceipt : Static.NingLiYBCOConstraintReceipt
existingStaticReceipt = Static.staticYBCO1997Constraint

existingRotatingReceipt : Rotating.RotatingFieldYBCOExperiment
existingRotatingReceipt = Rotating.canonicalRotatingFieldExperiment

sourceDataReplayPaysStaticBound : Bool
sourceDataReplayPaysStaticBound = true

sourceDataReplayPaysRotatingGeometry : Bool
sourceDataReplayPaysRotatingGeometry = true

sourceDataReplayPaysPositiveAntigravity : Bool
sourceDataReplayPaysPositiveAntigravity = false

sourceDataReplayPaysArmyApparatusIdentity : Bool
sourceDataReplayPaysArmyApparatusIdentity = false
