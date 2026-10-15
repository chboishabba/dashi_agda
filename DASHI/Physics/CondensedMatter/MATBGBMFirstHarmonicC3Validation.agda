module DASHI.Physics.CondensedMatter.MATBGBMFirstHarmonicC3Validation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Algebra.TriadicDepthOneCharacters as C3
import DASHI.Physics.CondensedMatter.MATBGBMFirstHarmonicC3Exact as BM

threeHarmonicRotationCloses :
  (h : BM.MoireHarmonic) →
  BM.rotateHarmonic (BM.rotateHarmonic (BM.rotateHarmonic h)) ≡ h
threeHarmonicRotationCloses = BM.rotateHarmonicCubed

lowerOffDiagonalIsConjugate :
  (v : BM.Valley) (h : BM.MoireHarmonic) →
  BM.lowerOffDiagonalPhase v h
    ≡ C3.conjugatePhase (BM.upperOffDiagonalPhase v h)
lowerOffDiagonalIsConjugate = BM.lowerIsConjugateUpper

timeReversalConjugatesUpperPhase :
  (v : BM.Valley) (h : BM.MoireHarmonic) →
  BM.upperOffDiagonalPhase (BM.timeReverseValley v) h
    ≡ C3.conjugatePhase (BM.upperOffDiagonalPhase v h)
timeReversalConjugatesUpperPhase = BM.timeReversalConjugatesUpper

c3RotationAdvancesUpperByValleyCharacter :
  (v : BM.Valley) (h : BM.MoireHarmonic) →
  BM.upperOffDiagonalPhase v (BM.rotateHarmonic h)
    ≡ C3.multiplyPhase
        (BM.valleyRotationCharacter v)
        (BM.upperOffDiagonalPhase v h)
c3RotationAdvancesUpperByValleyCharacter = BM.upperPhaseRotationLaw

firstHarmonicModelDoesNotPayInteractingSelfEnergy :
  BM.interactingSelfEnergyPaid BM.canonicalBMFirstHarmonicBoundary ≡ false
firstHarmonicModelDoesNotPayInteractingSelfEnergy = refl

firstHarmonicModelDoesNotPaySampleCalibration :
  BM.sampleParameterCalibrationPaid BM.canonicalBMFirstHarmonicBoundary ≡ false
firstHarmonicModelDoesNotPaySampleCalibration = refl
