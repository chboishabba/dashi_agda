module DASHI.Mathematics.NumberTheory.EisensteinLatticeCountingValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (+_)

import DASHI.Mathematics.NumberTheory.EisensteinLatticeCountingExact as E
import DASHI.Mathematics.NumberTheory.EisensteinLatticeQuadraticMaxCutExact as Q

triangularTen : E.triangularNumber 10 ≡ 55
triangularTen = refl

hexRadiusThree : E.hexBallCount 3 ≡ 37
hexRadiusThree = refl

wedgeThroughThree : E.wedgeTriangleCount 3 ≡ 10
wedgeThroughThree = refl

pascalFourTwo : E.choose 4 2 ≡ 6
pascalFourTwo = refl

normShellOne : E.eisensteinDivisorShellCount 1 ≡ 6
normShellOne = refl
normShellTwo : E.eisensteinDivisorShellCount 2 ≡ 0
normShellTwo = refl
normShellThree : E.eisensteinDivisorShellCount 3 ≡ 6
normShellThree = refl
normShellFour : E.eisensteinDivisorShellCount 4 ≡ 6
normShellFour = refl
normShellFive : E.eisensteinDivisorShellCount 5 ≡ 0
normShellFive = refl
normShellSix : E.eisensteinDivisorShellCount 6 ≡ 0
normShellSix = refl
normShellSeven : E.eisensteinDivisorShellCount 7 ≡ 12
normShellSeven = refl
normShellEight : E.eisensteinDivisorShellCount 8 ≡ 0
normShellEight = refl
normShellNine : E.eisensteinDivisorShellCount 9 ≡ 6
normShellNine = refl
normShellTen : E.eisensteinDivisorShellCount 10 ≡ 0
normShellTen = refl

integerNormUnit : Q.q (+ 1) (+ 0) ≡ + 1
integerNormUnit = refl
rotationPreservesSampleNorm : Q.q ((+ 2) - (+ 1)) (+ 2) ≡ Q.q (+ 2) (+ 1)
rotationPreservesSampleNorm = Q.rotateNormInvariant (+ 2) (+ 1)
