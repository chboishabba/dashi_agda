module DASHI.Mathematics.NumberTheory.EisensteinLatticeCountingValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Mathematics.NumberTheory.EisensteinLatticeCountingExact as E

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
