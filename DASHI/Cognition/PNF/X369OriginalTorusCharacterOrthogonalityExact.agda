module DASHI.Cognition.PNF.X369OriginalTorusCharacterOrthogonalityExact where

-- Exact C3 x C3 nine-character ORTHOGONALITY on the ORIGINAL
-- FiniteThreeCycleTorusExact.Torus3x3 carrier.
-- No duplicate nine-element torus, no floating cyclotomic approximations.
-- The original character table and enumeration are reused.
--
-- The target is the exact Eisenstein integer lattice Z[omega] where
-- omega^2 + omega + 1 = 0. This finite cancellation does NOT imply
-- a continuum Fourier transform, Leech lattice action, trained
-- neural phase, Monster representation, NS, YM, or physical dynamics.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer using (ℤ; +_; -_; _+_)

import DASHI.Physics.Common.FiniteThreeCycleTorusExact as Torus
import DASHI.Biology.BalancedTernaryFourierModeExact as Fourier
import DASHI.Algebra.TriadicDepthOneCharacters as Characters

record Eisenstein : Set where
  constructor eisenstein
  field
    integerPart : ℤ
    omegaPart : ℤ

zeroE : Eisenstein
zeroE = eisenstein (+ 0) (+ 0)

nineE : Eisenstein
nineE = eisenstein (+ 9) (+ 0)

addE : Eisenstein → Eisenstein → Eisenstein
addE (eisenstein a b) (eisenstein c d) =
  eisenstein (a + c) (b + d)

phaseE : Characters.C3Phase → Eisenstein
phaseE Characters.phase0 = eisenstein (+ 1) (+ 0)
phaseE Characters.phase1 = eisenstein (+ 0) (+ 1)
phaseE Characters.phase2 = eisenstein (- (+ 1)) (- (+ 1))

combinedCharacter : Torus.Torus3x3 → Torus.Torus3x3 →
                    Characters.C3Phase
combinedCharacter mode point =
  Characters.multiplyPhase (Fourier.firstCharacter mode point)
                           (Fourier.secondCharacter mode point)

orthogonalitySummand : Torus.Torus3x3 → Torus.Torus3x3 →
                        Torus.Torus3x3 → Eisenstein
orthogonalitySummand left right point =
  phaseE (Characters.multiplyPhase (combinedCharacter left point)
          (Characters.conjugatePhase (combinedCharacter right point)))

sumFiniteOriginalTorus : (Torus.Torus3x3 → Eisenstein) →
                         List Torus.Torus3x3 → Eisenstein
sumFiniteOriginalTorus f [] = zeroE
sumFiniteOriginalTorus f (point ∷ points) =
  addE (f point) (sumFiniteOriginalTorus f points)

originalTorusCharacterInner : Torus.Torus3x3 →
                               Torus.Torus3x3 → Eisenstein
originalTorusCharacterInner left right =
  sumFiniteOriginalTorus (orthogonalitySummand left right)
                         Fourier.canonicalModes

sameResidue : Torus.Residue3 → Torus.Residue3 → Bool
sameResidue Torus.residueMinus Torus.residueMinus = true
sameResidue Torus.residueZero Torus.residueZero = true
sameResidue Torus.residuePlus Torus.residuePlus = true
sameResidue _ _ = false

andBool : Bool → Bool → Bool
andBool true y = y
andBool false _ = false

sameOriginalPoint : Torus.Torus3x3 → Torus.Torus3x3 → Bool
sameOriginalPoint left right =
  andBool (sameResidue (Torus.firstCoordinate left)
                       (Torus.firstCoordinate right))
          (sameResidue (Torus.secondCoordinate left)
                       (Torus.secondCoordinate right))

diagonalTarget : Bool → Eisenstein
diagonalTarget true = nineE
diagonalTarget false = zeroE

-- 81 reflexive exact integer normalisation cases, no postulates and no
-- floating comparisons. Agda pinned-toolchain replay is still required.
originalTorusC3SquareCharacterOrthogonality :
  (left right : Torus.Torus3x3) →
  originalTorusCharacterInner left right ≡
  diagonalTarget (sameOriginalPoint left right)

originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueMinus Torus.residueMinus)
  (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueMinus Torus.residueMinus)
  (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueMinus Torus.residueMinus)
  (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueMinus Torus.residueMinus)
  (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueMinus Torus.residueMinus)
  (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueMinus Torus.residueMinus)
  (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueMinus Torus.residueMinus)
  (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueMinus Torus.residueMinus)
  (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueMinus Torus.residueMinus)
  (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueMinus Torus.residueZero)
  (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueMinus Torus.residueZero)
  (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueMinus Torus.residueZero)
  (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueMinus Torus.residueZero)
  (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueMinus Torus.residueZero)
  (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueMinus Torus.residueZero)
  (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueMinus Torus.residueZero)
  (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueMinus Torus.residueZero)
  (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueMinus Torus.residueZero)
  (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueMinus Torus.residuePlus)
  (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueMinus Torus.residuePlus)
  (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueMinus Torus.residuePlus)
  (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueMinus Torus.residuePlus)
  (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueMinus Torus.residuePlus)
  (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueMinus Torus.residuePlus)
  (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueMinus Torus.residuePlus)
  (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueMinus Torus.residuePlus)
  (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueMinus Torus.residuePlus)
  (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueZero Torus.residueMinus)
  (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueZero Torus.residueMinus)
  (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueZero Torus.residueMinus)
  (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueZero Torus.residueMinus)
  (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueZero Torus.residueMinus)
  (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueZero Torus.residueMinus)
  (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueZero Torus.residueMinus)
  (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueZero Torus.residueMinus)
  (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueZero Torus.residueMinus)
  (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueZero Torus.residueZero)
  (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueZero Torus.residueZero)
  (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueZero Torus.residueZero)
  (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueZero Torus.residueZero)
  (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueZero Torus.residueZero)
  (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueZero Torus.residueZero)
  (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueZero Torus.residueZero)
  (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueZero Torus.residueZero)
  (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueZero Torus.residueZero)
  (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueZero Torus.residuePlus)
  (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueZero Torus.residuePlus)
  (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueZero Torus.residuePlus)
  (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueZero Torus.residuePlus)
  (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueZero Torus.residuePlus)
  (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueZero Torus.residuePlus)
  (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueZero Torus.residuePlus)
  (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueZero Torus.residuePlus)
  (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residueZero Torus.residuePlus)
  (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residuePlus Torus.residueMinus)
  (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residuePlus Torus.residueMinus)
  (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residuePlus Torus.residueMinus)
  (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residuePlus Torus.residueMinus)
  (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residuePlus Torus.residueMinus)
  (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residuePlus Torus.residueMinus)
  (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residuePlus Torus.residueMinus)
  (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residuePlus Torus.residueMinus)
  (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residuePlus Torus.residueMinus)
  (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residuePlus Torus.residueZero)
  (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residuePlus Torus.residueZero)
  (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residuePlus Torus.residueZero)
  (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residuePlus Torus.residueZero)
  (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residuePlus Torus.residueZero)
  (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residuePlus Torus.residueZero)
  (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residuePlus Torus.residueZero)
  (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residuePlus Torus.residueZero)
  (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residuePlus Torus.residueZero)
  (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residuePlus Torus.residuePlus)
  (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residuePlus Torus.residuePlus)
  (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residuePlus Torus.residuePlus)
  (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residuePlus Torus.residuePlus)
  (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residuePlus Torus.residuePlus)
  (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residuePlus Torus.residuePlus)
  (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residuePlus Torus.residuePlus)
  (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residuePlus Torus.residuePlus)
  (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalTorusC3SquareCharacterOrthogonality
  (Torus.torusPoint Torus.residuePlus Torus.residuePlus)
  (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
