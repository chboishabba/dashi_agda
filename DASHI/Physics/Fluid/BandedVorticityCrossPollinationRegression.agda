module DASHI.Physics.Fluid.BandedVorticityCrossPollinationRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

open import DASHI.Foundations.SSPTritCarrier using
  (sspNegOne; sspZero; sspPosOne)
open import DASHI.Physics.Fluid.BandedVorticitySpinTwist
open import DASHI.Physics.Fluid.BandedVorticityCrossPollination

negativeAtom : VortexAtom
negativeAtom = vortexAtom midBand (site 8 13) sspNegOne refl 2 9

positiveAtom : VortexAtom
positiveAtom = vortexAtom highBand (site 9 13) sspPosOne refl 1 6

supportSignNegativeRoundtrip :
  assembleSpin (factorSpin sspNegOne) ≡ sspNegOne
supportSignNegativeRoundtrip = refl

supportSignNeutralRoundtrip :
  assembleSpin (factorSpin sspZero) ≡ sspZero
supportSignNeutralRoundtrip = refl

supportSignPositiveRoundtrip :
  assembleSpin (factorSpin sspPosOne) ≡ sspPosOne
supportSignPositiveRoundtrip = refl

negativeMirrorIsPositive : mirrorSpin sspNegOne ≡ sspPosOne
negativeMirrorIsPositive = refl

positiveMirrorIsNegative : mirrorSpin sspPosOne ≡ sspNegOne
positiveMirrorIsNegative = refl

neutralMirrorIsNeutral : mirrorSpin sspZero ≡ sspZero
neutralMirrorIsNeutral = refl

negativeMirrorTwice : mirrorSpin (mirrorSpin sspNegOne) ≡ sspNegOne
negativeMirrorTwice = refl

canonicalAddressedAtom : AddressedVortexAtom
canonicalAddressedAtom = addressVortex negativeAtom

canonicalTrack : VortexWorldTube
canonicalTrack =
  mkCandidateVortexWorldTube
    42
    (timedAtom 0 42 negativeAtom
     ∷ timedAtom 1 42 positiveAtom
     ∷ [])
    "candidate coherent-vortex track across two frames"

canonicalSelectionReceipt : SolverSelectionReceipt
canonicalSelectionReceipt =
  mkExternalSolverSelection
    12
    31
    27
    vortexFaithfulMode
    "choose faithful mode when coherence-loss penalty exceeds atom cost"

canonicalSelectedMode :
  selectedSolverMode canonicalSelectionReceipt ≡ vortexFaithfulMode
canonicalSelectedMode = refl

canonicalTubeIsModelled : tubeIdentityIsModelled canonicalTrack ≡ true
canonicalTubeIsModelled = refl

canonicalTubeIsNotExactContinuumFact :
  tubeIdentityIsExactContinuumFact canonicalTrack ≡ false
canonicalTubeIsNotExactContinuumFact = refl
