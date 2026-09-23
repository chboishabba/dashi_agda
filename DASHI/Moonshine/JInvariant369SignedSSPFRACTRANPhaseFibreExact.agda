module DASHI.Moonshine.JInvariant369SignedSSPFRACTRANPhaseFibreExact where

------------------------------------------------------------------------
-- SIGNED SSP / FRACTRAN IN THE CANONICAL 369 FIBRED INTERPRETATION
--
-- Existing theorem-bearing seams:
--
--   SignedSSPFRACTRANWeaveExact
--     signed multiplicity -> coarse {-1,0,+1} orientation;
--
--   JInvariantColourWheelWaveSignedBidiExact
--     signed multiplicity negation -> C3 spectral conjugation;
--
--   JInvariant369CanonicalLevelObserverTowerExact
--     the principal-level C3 cusp fibre carries fixed-point-free translation.
--
-- The important conclusion is typed:
--
--   signed SSP/FRACTRAN naturally inhabits the phase/spectral C3 lane.
--
-- It is NOT automatically the principal-level C3 cusp fibre.  In fact there
-- cannot be an action-intertwining map that sends spectral conjugation to the
-- nontrivial level-3 translation, because spectral zero is fixed by
-- conjugation while level-3 translation has no fixed point.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Moonshine.JInvariantColourWheelWaveSignedBidiExact as SignedJ
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Spectral
import DASHI.Moonshine.JInvariant369CanonicalLevelObserverTowerExact as LevelTower
import DASHI.Moonshine.JInvariant369PhaseLevelSeparationExact as Separation
import DASHI.Moonshine.JInvariant369ModularLevelCuspObserversExact as Level

------------------------------------------------------------------------
-- 1. Existing signed arithmetic really does land in the spectral C3 observer.
------------------------------------------------------------------------

signedSSPPhaseObserver :
  Signed.SignedMultiplicity →
  Spectral.AxisFrequency
signedSSPPhaseObserver =
  SignedJ.signedMultiplicityFrequency

signedSSPNegationIsSpectralConjugation :
  (m : Signed.SignedMultiplicity) →
  signedSSPPhaseObserver (Signed.negateMultiplicity m)
  ≡
  Spectral.conjugateFrequency (signedSSPPhaseObserver m)
signedSSPNegationIsSpectralConjugation =
  SignedJ.signedNegationBecomesSpectralConjugation

signedSSPPhaseRecoversOrientation :
  (m : Signed.SignedMultiplicity) →
  SignedJ.frequencyToFRACTRANOrientation
    (signedSSPPhaseObserver m)
  ≡
  Signed.orientationOfMultiplicity m
signedSSPPhaseRecoversOrientation =
  SignedJ.spectralObserverRecoversFRACTRANOrientation

------------------------------------------------------------------------
-- 2. The spectral action has a fixed point.
------------------------------------------------------------------------

spectralZeroIsConjugationFixed :
  Spectral.conjugateFrequency Spectral.frequencyZero
  ≡ Spectral.frequencyZero
spectralZeroIsConjugationFixed = refl

------------------------------------------------------------------------
-- 3. No action-intertwining collapse into the principal-level C3 translation.
------------------------------------------------------------------------

record SignedPhaseToLevel3Intertwiner : Set where
  field
    calibrate :
      Spectral.AxisFrequency →
      Level.level3CuspFibre

    intertwines :
      (frequency : Spectral.AxisFrequency) →
      calibrate (Spectral.conjugateFrequency frequency)
      ≡
      LevelTower.translateLevel3Residue (calibrate frequency)

open SignedPhaseToLevel3Intertwiner public

signedSpectralConjugationCannotEqualLevel3Translation :
  SignedPhaseToLevel3Intertwiner →
  Separation.Empty
signedSpectralConjugationCannotEqualLevel3Translation bridge =
  Separation.level3TranslationNoFixedPoint
    (calibrate bridge Spectral.frequencyZero)
    (sym
      (trans
        (cong (calibrate bridge) spectralZeroIsConjugationFixed)
        (intertwines bridge Spectral.frequencyZero)))

------------------------------------------------------------------------
-- 4. Consequently signed SSP is an input to the phase/spectral fibre, not a
--    proof of the principal-level coordinate.
------------------------------------------------------------------------

record SignedSSP369FibreBoundary : Set where
  constructor signed-ssp-369-fibre-boundary
  field
    signedMultiplicityHasCoarseC3Observer : Bool
    signedNegationIntertwinesSpectralConjugation : Bool
    spectralObserverRecoversSignedOrientation : Bool

    spectralConjugationHasFixedZero : Bool
    level3TranslationFixedPointFree : Bool
    conjugationToLevelTranslationIntertwinerExists : Bool

    signedSSPNaturallyBelongsToPhaseSpectralLane : Bool
    signedSSPAutomaticallyIsPrincipalLevel3Fibre : Bool
    signedMagnitudeEqualsSpectralAmplitude : Bool

open SignedSSP369FibreBoundary public

canonicalSignedSSP369FibreBoundary :
  SignedSSP369FibreBoundary
canonicalSignedSSP369FibreBoundary =
  signed-ssp-369-fibre-boundary
    true true true
    true true false
    true false false
