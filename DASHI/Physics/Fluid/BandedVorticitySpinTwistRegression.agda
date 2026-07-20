module DASHI.Physics.Fluid.BandedVorticitySpinTwistRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

open import DASHI.Foundations.SSPTritCarrier using
  (sspNegOne; sspPosOne)
open import DASHI.Physics.Fluid.BandedVorticitySpinTwist

------------------------------------------------------------------------
-- Canonical executable witnesses for the two-mode carrier.

negativeMidAtom : VortexAtom
negativeMidAtom =
  vortexAtom midBand (site 12 17) sspNegOne refl 2 7

positiveHighAtom : VortexAtom
positiveHighAtom =
  vortexAtom highBand (site 31 9) sspPosOne refl 1 4

canonicalEnergy : BandEnergySummary ∷ BandEnergySummary ∷ []
canonicalEnergy = bandEnergy midBand 11 ∷ bandEnergy highBand 5 ∷ []

canonicalLowCarrier : LowBandCarrier
canonicalLowCarrier =
  lowCarrier
    "retained low Fourier coefficients plus banded spin/twist samples"
    (bandedSpinTwist lowBand (site 4 4) sspPosOne 3 ∷ [])

canonicalFaithfulResidual : FaithfulResidualState
canonicalFaithfulResidual =
  faithfulResidual
    canonicalEnergy
    23
    (negativeMidAtom ∷ positiveHighAtom ∷ [])

canonicalFaithfulState : VortexFaithfulSolverState
canonicalFaithfulState =
  vortexFaithfulState canonicalLowCarrier canonicalFaithfulResidual

canonicalFastState : FastSolverState
canonicalFastState = eraseFaithfulState 99 canonicalFaithfulState

canonicalErasureKeepsLowCarrier :
  fastLowCarrier canonicalFastState ≡ canonicalLowCarrier
canonicalErasureKeepsLowCarrier = refl

canonicalErasureKeepsEnergy :
  fastBandEnergy (fastResidual canonicalFastState) ≡ canonicalEnergy
canonicalErasureKeepsEnergy = refl

canonicalErasureKeepsSupportSummary :
  fastSupportFraction (fastResidual canonicalFastState) ≡ 23
canonicalErasureKeepsSupportSummary = refl

canonicalFastCapability : SolverCapability fastMode
canonicalFastCapability = fastModeHasAggregateCapability

canonicalFaithfulCapability : SolverCapability vortexFaithfulMode
canonicalFaithfulCapability = faithfulModeHasVortexCapability
