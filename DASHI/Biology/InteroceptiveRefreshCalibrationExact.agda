module DASHI.Biology.InteroceptiveRefreshCalibrationExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- Literature calibration:
-- A. D. (Bud) Craig,
-- "How do you feel -- now? The anterior insula and human awareness",
-- DOI 10.1038/nrn2555.
--
-- Craig discusses an approximately 125 ms framing/re-representation timescale.
-- We record it as a candidate calibration constant only.  It is not promoted to
-- a universal cortical, interoceptive, or phenomenal refresh law.
------------------------------------------------------------------------

candidateRefreshMilliseconds : Nat
candidateRefreshMilliseconds = 125

candidateCalibrationPinned : candidateRefreshMilliseconds ≡ 125
candidateCalibrationPinned = refl

record InteroceptiveRefreshBoundary : Set where
  constructor interoceptiveRefreshBoundary
  field
    oneRefreshPeriodUniversalAcrossBrainsAndContexts : Bool
    candidateTimescaleMayCalibrateFiniteModel : Bool

canonicalInteroceptiveRefreshBoundary : InteroceptiveRefreshBoundary
canonicalInteroceptiveRefreshBoundary =
  interoceptiveRefreshBoundary false false
