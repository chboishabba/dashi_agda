module DASHI.Physics.Closure.NSTriadKNPeriodicFourierStrainInterferenceRound35Exact where

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
-- Turn the Round-34 modewise half-isometry and the Round-35 polarized Gram
-- formula into an exact finite interference decomposition.  For any finite
-- family of transverse vorticity modes,
--
--   || sum_k S_k omega_k ||_F^2
--     = (1/2) sum_k |omega_k|^2
--       + 2 sum_{k<l} <S_k omega_k,S_l omega_l>_F.
--
-- Consequently every departure from the exact diagonal half-energy is a
-- cross-fibre term.  This is the algebraic form needed by the geometric
-- HH-good programme: same-fibre stretching has already depleted exactly, so
-- the remaining analytic task is to control the explicit interference sum by
-- directional/kernel increment information.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as Matrix
import DASHI.Physics.Closure.NSTriadKNPeriodicFourierStrainMultiplierRound34Exact as Strain
import DASHI.Physics.Closure.NSTriadKNPeriodicFourierStrainGramRound35Exact as Gram

record TransverseStrainMode : Set where
  constructor transverse-strain-mode
  field
    modeData : V.ProjectionMode
    omega : V.Vector3
    transverse : V.dot (V.mode modeData) omega ≡ 0ℚ

open TransverseStrainMode public

strainOf : TransverseStrainMode → Matrix.Matrix3
strainOf item = Strain.fourierStrain (modeData item) (omega item)

zeroMatrix : Matrix.Matrix3
zeroMatrix = Matrix.matrix3
  0ℚ 0ℚ 0ℚ
  0ℚ 0ℚ 0ℚ
  0ℚ 0ℚ 0ℚ

matrixAdd : Matrix.Matrix3 → Matrix.Matrix3 → Matrix.Matrix3
matrixAdd left right = Matrix.matrix3
  (Matrix.m11 left + Matrix.m11 right)
  (Matrix.m12 left + Matrix.m12 right)
  (Matrix.m13 left + Matrix.m13 right)
  (Matrix.m21 left + Matrix.m21 right)
  (Matrix.m22 left + Matrix.m22 right)
  (Matrix.m23 left + Matrix.m23 right)
  (Matrix.m31 left + Matrix.m31 right)
  (Matrix.m32 left + Matrix.m32 right)
  (Matrix.m33 left + Matrix.m33 right)

frobeniusSquaredZero : Strain.frobeniusSquared zeroMatrix ≡ 0ℚ
frobeniusSquaredZero = solve []

frobeniusSquaredAdd :
  ∀ left right →
  Strain.frobeniusSquared (matrixAdd left right)
  ≡ Strain.frobeniusSquared left
    + Strain.frobeniusSquared right
    + Strain.two * Gram.frobeniusInner left right
frobeniusSquaredAdd left right =
  solve
    ( Matrix.m11 left ∷ Matrix.m12 left ∷ Matrix.m13 left
    ∷ Matrix.m21 left ∷ Matrix.m22 left ∷ Matrix.m23 left
    ∷ Matrix.m31 left ∷ Matrix.m32 left ∷ Matrix.m33 left
    ∷ Matrix.m11 right ∷ Matrix.m12 right ∷ Matrix.m13 right
    ∷ Matrix.m21 right ∷ Matrix.m22 right ∷ Matrix.m23 right
    ∷ Matrix.m31 right ∷ Matrix.m32 right ∷ Matrix.m33 right
    ∷ [])

frobeniusInnerAddRight :
  ∀ left first second →
  Gram.frobeniusInner left (matrixAdd first second)
  ≡ Gram.frobeniusInner left first + Gram.frobeniusInner left second
frobeniusInnerAddRight left first second =
  solve
    ( Matrix.m11 left ∷ Matrix.m12 left ∷ Matrix.m13 left
    ∷ Matrix.m21 left ∷ Matrix.m22 left ∷ Matrix.m23 left
    ∷ Matrix.m31 left ∷ Matrix.m32 left ∷ Matrix.m33 left
    ∷ Matrix.m11 first ∷ Matrix.m12 first ∷ Matrix.m13 first
    ∷ Matrix.m21 first ∷ Matrix.m22 first ∷ Matrix.m23 first
    ∷ Matrix.m31 first ∷ Matrix.m32 first ∷ Matrix.m33 first
    ∷ Matrix.m11 second ∷ Matrix.m12 second ∷ Matrix.m13 second
    ∷ Matrix.m21 second ∷ Matrix.m22 second ∷ Matrix.m23 second
    ∷ Matrix.m31 second ∷ Matrix.m32 second ∷ Matrix.m33 second
    ∷ [])

frobeniusInnerZeroRight :
  ∀ left → Gram.frobeniusInner left zeroMatrix ≡ 0ℚ
frobeniusInnerZeroRight left =
  solve
    ( Matrix.m11 left ∷ Matrix.m12 left ∷ Matrix.m13 left
    ∷ Matrix.m21 left ∷ Matrix.m22 left ∷ Matrix.m23 left
    ∷ Matrix.m31 left ∷ Matrix.m32 left ∷ Matrix.m33 left
    ∷ [])

sumStrain : List TransverseStrainMode → Matrix.Matrix3
sumStrain [] = zeroMatrix
sumStrain (item ∷ items) = matrixAdd (strainOf item) (sumStrain items)

diagonalHalfEnergy : List TransverseStrainMode → ℚ
diagonalHalfEnergy [] = 0ℚ
diagonalHalfEnergy (item ∷ items) =
  Strain.half * V.normSquared (omega item)
  + diagonalHalfEnergy items

crossWithHead :
  TransverseStrainMode → List TransverseStrainMode → ℚ
crossWithHead head [] = 0ℚ
crossWithHead head (item ∷ items) =
  Strain.two * Gram.frobeniusInner (strainOf head) (strainOf item)
  + crossWithHead head items

crossInterference : List TransverseStrainMode → ℚ
crossInterference [] = 0ℚ
crossInterference (item ∷ items) =
  crossWithHead item items + crossInterference items

crossWithHeadIsInnerOfTail :
  ∀ head items →
  Strain.two * Gram.frobeniusInner (strainOf head) (sumStrain items)
  ≡ crossWithHead head items
crossWithHeadIsInnerOfTail head [] =
  trans
    (cong (Strain.two *_)
      (frobeniusInnerZeroRight (strainOf head)))
    (solve [])
crossWithHeadIsInnerOfTail head (item ∷ items) =
  trans
    (cong (Strain.two *_)
      (frobeniusInnerAddRight
        (strainOf head) (strainOf item) (sumStrain items)))
    (trans
      (solve
        ( Gram.frobeniusInner (strainOf head) (strainOf item)
        ∷ Gram.frobeniusInner (strainOf head) (sumStrain items)
        ∷ []))
      (cong
        (Strain.two * Gram.frobeniusInner
          (strainOf head) (strainOf item) +_)
        (crossWithHeadIsInnerOfTail head items)))

finiteStrainInterferenceDecomposition :
  ∀ items →
  Strain.frobeniusSquared (sumStrain items)
  ≡ diagonalHalfEnergy items + crossInterference items
finiteStrainInterferenceDecomposition [] =
  trans frobeniusSquaredZero (solve [])
finiteStrainInterferenceDecomposition (item ∷ items) =
  trans
    (frobeniusSquaredAdd (strainOf item) (sumStrain items))
    (trans
      (cong
        (λ diagonal →
          diagonal
          + Strain.frobeniusSquared (sumStrain items)
          + Strain.two * Gram.frobeniusInner
              (strainOf item) (sumStrain items))
        (Strain.fourierStrainFrobeniusTransverseExact
          (modeData item) (omega item) (transverse item)))
      (trans
        (cong
          (λ tailEnergy →
            Strain.half * V.normSquared (omega item)
            + tailEnergy
            + Strain.two * Gram.frobeniusInner
                (strainOf item) (sumStrain items))
          (finiteStrainInterferenceDecomposition items))
        (trans
          (cong
            (λ cross →
              Strain.half * V.normSquared (omega item)
              + (diagonalHalfEnergy items + crossInterference items)
              + cross)
            (crossWithHeadIsInnerOfTail item items))
          (solve
            ( Strain.half * V.normSquared (omega item)
            ∷ diagonalHalfEnergy items
            ∷ crossInterference items
            ∷ crossWithHead item items
            ∷ [])))))

periodicFiniteStrainInterferenceDecompositionClosed : Bool
periodicFiniteStrainInterferenceDecompositionClosed = true

physicalCrossFibreInterferenceDecayConstructed : Bool
physicalCrossFibreInterferenceDecayConstructed = false

periodicFiniteStrainInterferenceDecompositionClosedIsTrue :
  periodicFiniteStrainInterferenceDecompositionClosed ≡ true
periodicFiniteStrainInterferenceDecompositionClosedIsTrue = refl

physicalCrossFibreInterferenceDecayConstructedIsFalse :
  physicalCrossFibreInterferenceDecayConstructed ≡ false
physicalCrossFibreInterferenceDecayConstructedIsFalse = refl
