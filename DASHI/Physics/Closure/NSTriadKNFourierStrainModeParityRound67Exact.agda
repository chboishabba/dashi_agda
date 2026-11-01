module DASHI.Physics.Closure.NSTriadKNFourierStrainModeParityRound67Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman; Andrew J. Majda.
-- Title: "Geometric Constraints on Potentially Singular Solutions for the
-- 3-D Euler Equations".
-- DOI: 10.1080/03605309608821197.
--
-- Authors: J. Thomas Beale; Tosio Kato; Andrew Majda.
-- Title: "Remarks on the Breakdown of Smooth Solutions for the 3-D Euler
-- Equations".
-- DOI: 10.1007/BF01240221.
--
-- ROUND 67 / B3 LOW-OUTPUT BRANCH
--
-- Round66 exposes a low-output branch where p and q are the dominant modes and
-- k=p+q is low.  The useful Taylor pair there is p versus -q: their separation
-- is the low output k.  To use that pair without changing the physical symbol
-- one needs the mode parity of the strain multiplier.
--
-- This module proves that parity from the literal Round38 formula.  Negating a
-- projection mode preserves |k|^2 and its inverse, while the angular strain
-- contains two factors linear in k and is therefore even:
--
--     S_{-k}(omega) = S_k(omega).
--
-- Thus the low-output Bony branch may compare the two close dominant points
-- p and -q without paying a sign/parity error in the strain symbol.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as Matrix
import DASHI.Physics.Closure.NSTriadKNCorrectedFourierAngularStrainExact as Angular
import DASHI.Physics.Closure.NSTriadKNFourierStrainMultiplierRound38Exact as Strain

minusOne : ℚ
minusOne = - 1ℚ

normSquaredNegate : ∀ value →
  V.normSquared (V.scale minusOne value) ≡ V.normSquared value
normSquaredNegate (V.v3 x y z) =
  solve (x ∷ y ∷ z ∷ [])

negatedProjectionMode : V.ProjectionMode → V.ProjectionMode
negatedProjectionMode modeData =
  V.projection-mode
    (V.scale minusOne (V.mode modeData))
    (V.inverseNormSquared modeData)
    (trans
      (cong
        (V.inverseNormSquared modeData *_)
        (normSquaredNegate (V.mode modeData)))
      (V.inverseLaw modeData))

negatedProjectionModeMode : ∀ modeData →
  V.mode (negatedProjectionMode modeData)
  ≡ V.scale minusOne (V.mode modeData)
negatedProjectionModeMode modeData = refl

negatedProjectionModeInverse : ∀ modeData →
  V.inverseNormSquared (negatedProjectionMode modeData)
  ≡ V.inverseNormSquared modeData
negatedProjectionModeInverse modeData = refl

angularStrainEvenInMode : ∀ theta omega →
  Angular.angularStrain (V.scale minusOne theta) omega
  ≡ Angular.angularStrain theta omega
angularStrainEvenInMode
    (V.v3 tx ty tz) (V.v3 wx wy wz) =
  Matrix.matrixExt
    (solve (tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ Angular.minusHalf ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ Angular.minusHalf ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ Angular.minusHalf ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ Angular.minusHalf ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ Angular.minusHalf ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ Angular.minusHalf ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ Angular.minusHalf ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ Angular.minusHalf ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ Angular.minusHalf ∷ []))

fourierStrainMultiplierEvenInMode : ∀ modeData omega →
  Strain.fourierStrainMultiplier (negatedProjectionMode modeData) omega
  ≡ Strain.fourierStrainMultiplier modeData omega
fourierStrainMultiplierEvenInMode modeData omega =
  trans
    (Strain.fourierStrainMultiplierExact
      (negatedProjectionMode modeData) omega)
    (trans
      (cong
        (Strain.scaleMatrix (V.inverseNormSquared modeData))
        (angularStrainEvenInMode (V.mode modeData) omega))
      (sym (Strain.fourierStrainMultiplierExact modeData omega)))

round67LowOutputParitySeamClosed : Bool
round67LowOutputParitySeamClosed = true

round67LowOutputParitySeamClosedIsTrue :
  round67LowOutputParitySeamClosed ≡ true
round67LowOutputParitySeamClosedIsTrue = refl
