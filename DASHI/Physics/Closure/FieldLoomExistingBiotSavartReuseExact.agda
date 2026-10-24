module DASHI.Physics.Closure.FieldLoomExistingBiotSavartReuseExact where

------------------------------------------------------------------------
-- FIELD LOOM = CONSUMER OF AN EXISTING REPOSITORY PHYSICS OWNER
--
-- The law of magnetostatic current fields is historically Biot/Savart
-- (1820) and belongs to classical Maxwell magnetostatics, not DASHI.
-- Beale–Kato–Majda (1984) and Luo (2019) own the cited fluid/regularity
-- publications; those papers are NOT the source of magnetostatics.
--
-- Repo owners reused without redefinition:
--  NSTriadKNFourierBiotSavartExact:
--     rational amplitude |k|^-2 (k × source), transversality,
--     norm gain and phase-corrected inverse curl;
--  NSTriadKNMaxwellFluidBiotSavartBridgeExact:
--     scaled magnetic-field-from-current and fluid comparison.
-- MHDPhysicalInverseCurlMagneticHelicityExact owns the DISTINCT
-- complex/periodic physical curl and magnetic vector-potential lane.
--
-- This is a *thin theorem reuse adapter* for PR #1242.  The infinite/
-- periodic Fourier inversion has NOT been welded to a real-space thin
-- circular-wire quadrature, a source-current distribution, an absolute
-- SI normalization, a physical magnetic material, or coil measurements.
-- No formal proof in this file establishes a physical levitation force,
-- gravity modification, full Maxwell constitutive closure or hardware.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; 0ℚ)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNFourierBiotSavartExact as BS
import DASHI.Physics.Closure.NSTriadKNMaxwellFluidBiotSavartBridgeExact as Owner

fieldLoomFourierCurrentField :
  ℚ → V.ProjectionMode → V.Vector3 → V.Vector3
fieldLoomFourierCurrentField = Owner.magneticFieldFromCurrent

fieldLoomFourierCurrentIsTransverse :
  (coupling : ℚ) →
  (modeData : V.ProjectionMode) →
  (current : V.Vector3) →
  V.dot (V.mode modeData)
    (fieldLoomFourierCurrentField coupling modeData current)
  ≡ 0ℚ
fieldLoomFourierCurrentIsTransverse =
  Owner.coupledBiotSavartTransverse

fieldLoomMagneticFluidAmplitudeRelation :
  (coupling : ℚ) →
  (modeData : V.ProjectionMode) →
  (current : V.Vector3) →
  fieldLoomFourierCurrentField coupling modeData current
  ≡ V.scale coupling
      (Owner.fluidVelocityFromVorticity modeData current)
fieldLoomMagneticFluidAmplitudeRelation =
  Owner.magneticFluidRelation

fieldLoomFourierPhaseCorrectedInversion :
  (modeData : V.ProjectionMode) →
  (current : V.Vector3) →
  V.dot (V.mode modeData) current ≡ 0ℚ →
  BS.phaseCorrectedCurl (V.mode modeData)
    (BS.biotSavart modeData current)
  ≡ current
fieldLoomFourierPhaseCorrectedInversion =
  BS.phaseCorrectedCurlBiotSavart

-- No separate result for filament-current geometry is manufactured here.
-- S1 real-space quadrature remains the existing
-- scripts/psychotronics_field_loom_coils.py numeric producer, tested
-- independently against analytic on-axis and elliptic-integral loop fields.
