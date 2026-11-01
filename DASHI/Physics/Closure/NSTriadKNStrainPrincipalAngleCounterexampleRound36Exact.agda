module DASHI.Physics.Closure.NSTriadKNStrainPrincipalAngleCounterexampleRound36Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Peter Constantin; Charles Fefferman; Andrew J. Majda.
-- Title: "Geometric Constraints on Potentially Singular Solutions for the
-- 3-D Euler Equations".
-- DOI: 10.1080/03605309608821197.
--
-- DASHI CONTRIBUTION
--
-- Round 35 identified sqrt(2) S_k as an isometry on each transverse fibre and
-- suggested controlling HH-good by principal angles between the images of
-- different fibres.  This module performs the first exact test of that idea.
--
-- Take orthogonal Fourier directions
--
--   k = e1,  l = e2,
--
-- and the common transverse vector omega = eta = e3.  Both mode norms are one
-- and k.l = 0, but the exact doubled cross-fibre Gram is
--
--   2 <S_e1 e3, S_e2 e3>_F = -1.
--
-- Thus the normalized strain images have a unit-magnitude correlation even
-- when the wave-vector directions are orthogonal.  Mode-angle separation by
-- itself therefore cannot be the missing HH-good smallness mechanism.  Any
-- successful principal-angle estimate must use more structure (spatial
-- increments, vorticity direction, shell localization, or the periodic PV
-- kernel), not merely k.l being small.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNPeriodicFourierStrainMultiplierRound34Exact as Strain
import DASHI.Physics.Closure.NSTriadKNPeriodicFourierStrainGramRound35Exact as Gram

e1 e2 e3 : V.Vector3
e1 = V.v3 1ℚ 0ℚ 0ℚ
e2 = V.v3 0ℚ 1ℚ 0ℚ
e3 = V.v3 0ℚ 0ℚ 1ℚ

e1Mode : V.ProjectionMode
e1Mode = V.projection-mode e1 1ℚ (solve [])

e2Mode : V.ProjectionMode
e2Mode = V.projection-mode e2 1ℚ (solve [])

modeDirectionsOrthogonal :
  V.dot (V.mode e1Mode) (V.mode e2Mode) ≡ 0ℚ
modeDirectionsOrthogonal = solve []

e3TransverseToE1 : V.dot (V.mode e1Mode) e3 ≡ 0ℚ
e3TransverseToE1 = solve []

e3TransverseToE2 : V.dot (V.mode e2Mode) e3 ≡ 0ℚ
e3TransverseToE2 = solve []

sameFibreNormalizedE1 :
  Strain.two
    * Gram.frobeniusInner
        (Strain.fourierStrain e1Mode e3)
        (Strain.fourierStrain e1Mode e3)
  ≡ 1ℚ
sameFibreNormalizedE1 =
  trans
    (Gram.twiceFourierStrainTransversePolarization
      e1Mode e3 e3 e3TransverseToE1 e3TransverseToE1)
    (solve [])

sameFibreNormalizedE2 :
  Strain.two
    * Gram.frobeniusInner
        (Strain.fourierStrain e2Mode e3)
        (Strain.fourierStrain e2Mode e3)
  ≡ 1ℚ
sameFibreNormalizedE2 =
  trans
    (Gram.twiceFourierStrainTransversePolarization
      e2Mode e3 e3 e3TransverseToE2 e3TransverseToE2)
    (solve [])

orthogonalModesUnitCrossCoherence :
  Strain.two
    * Gram.frobeniusInner
        (Strain.fourierStrain e1Mode e3)
        (Strain.fourierStrain e2Mode e3)
  ≡ - 1ℚ
orthogonalModesUnitCrossCoherence =
  trans
    (cong (Strain.two *_)
      (Gram.fourierStrainCrossFibreGramExact
        e1Mode e2Mode e3 e3))
    (solve [])

principalAngleModeSeparationAloneRefuted : Bool
principalAngleModeSeparationAloneRefuted = true

physicalPVIncrementCoherenceEstimateConstructed : Bool
physicalPVIncrementCoherenceEstimateConstructed = false

principalAngleModeSeparationAloneRefutedIsTrue :
  principalAngleModeSeparationAloneRefuted ≡ true
principalAngleModeSeparationAloneRefutedIsTrue = refl

physicalPVIncrementCoherenceEstimateConstructedIsFalse :
  physicalPVIncrementCoherenceEstimateConstructed ≡ false
physicalPVIncrementCoherenceEstimateConstructedIsFalse = refl
