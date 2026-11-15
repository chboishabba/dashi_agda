module DASHI.Physics.GR.SchutzholdPureModeSensitivityExact where

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; 0ℚ; ½; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

------------------------------------------------------------------------
-- PURE-MODE MAX-CUT
--
-- Schuetzhold Eq. (5):
--   Edot = hdot (Y - X)
-- after the spatial expectation/integral is packaged into X,Y.
-- For a pure x-directed pulse, Y=0.  Time-averaged free radiation has equal
-- electric and magnetic energy, so E = 2 X.  Therefore Edot = - hdot E/2.
-- The y-directed case is the opposite sign.  This derives the average bound
-- saturation algebra used by the half-cycle estimate rather than leaving it as
-- an anonymous numerical receipt.
------------------------------------------------------------------------

energyTransferRate : ℚ → ℚ → ℚ → ℚ
energyTransferRate hdot X Y = hdot * (Y - X)

pureXTotalEnergy : ℚ → ℚ
pureXTotalEnergy X = X + X

pureYTotalEnergy : ℚ → ℚ
pureYTotalEnergy Y = Y + Y

pureXAverageTransferIdentity :
  ∀ hdot X →
  energyTransferRate hdot X 0ℚ
  ≡ 0ℚ - ½ * hdot * pureXTotalEnergy X
pureXAverageTransferIdentity = solve-∀

pureYAverageTransferIdentity :
  ∀ hdot Y →
  energyTransferRate hdot 0ℚ Y
  ≡ ½ * hdot * pureYTotalEnergy Y
pureYAverageTransferIdentity = solve-∀

------------------------------------------------------------------------
-- LASTING FREQUENCY / PHASE READOUT
--
-- Pure x/y propagation gives opposite single-arm shifts +/- h Omega/2.
-- Therefore the arm-to-arm beat angular-frequency separation is h Omega, and
-- after a common delay tau the relative phase is h Omega tau.
------------------------------------------------------------------------

singleArmShift : ℚ → ℚ → ℚ
singleArmShift h omega = ½ * h * omega

oppositeArmShift : ℚ → ℚ → ℚ
oppositeArmShift h omega = 0ℚ - singleArmShift h omega

relativeAngularFrequencyShift : ℚ → ℚ → ℚ
relativeAngularFrequencyShift h omega =
  singleArmShift h omega - oppositeArmShift h omega

relativeShiftIsHtimesOmega :
  ∀ h omega → relativeAngularFrequencyShift h omega ≡ h * omega
relativeShiftIsHtimesOmega = solve-∀

relativePhaseAfterDelay : ℚ → ℚ → ℚ → ℚ
relativePhaseAfterDelay h omega tau =
  relativeAngularFrequencyShift h omega * tau

relativePhaseIsHOmegaTau :
  ∀ h omega tau →
  relativePhaseAfterDelay h omega tau ≡ h * omega * tau
relativePhaseIsHOmegaTau = solve-∀

------------------------------------------------------------------------
-- MULTI-HALF-CYCLE COHERENT ACCUMULATION
--
-- If each controlled half-cycle preserves the desired sign and contributes
-- h E/2, n half-cycles contribute n h E/2.  We isolate the scalar identity;
-- timing/coherence is a separate physical hypothesis.
------------------------------------------------------------------------

halfCycleEnergyMagnitude : ℚ → ℚ → ℚ
halfCycleEnergyMagnitude h energy = ½ * h * energy

twoHalfCycleEnergyMagnitude : ℚ → ℚ → ℚ
twoHalfCycleEnergyMagnitude h energy =
  halfCycleEnergyMagnitude h energy + halfCycleEnergyMagnitude h energy

twoHalfCyclesGiveHE :
  ∀ h energy → twoHalfCycleEnergyMagnitude h energy ≡ h * energy
twoHalfCyclesGiveHE = solve-∀

record PureModeSensitivityScope : Set where
  constructor pure-mode-sensitivity-scope
  field
    averageTransferHalfBoundDerivedForPureMode : Bool
    oppositeArmBeatShiftDerived : Bool
    delayedRelativePhaseFormulaDerived : Bool
    twoHalfCycleHEAccumulationDerived : Bool
    timingCoherenceStillExperimental : Bool
    cavityLossNoiseStillExperimental : Bool

canonicalPureModeSensitivityScope : PureModeSensitivityScope
canonicalPureModeSensitivityScope =
  pure-mode-sensitivity-scope true true true true true true
