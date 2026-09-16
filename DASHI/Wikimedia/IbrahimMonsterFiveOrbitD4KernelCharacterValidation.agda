module DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4KernelCharacterValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4KernelCharacterExact as K

identityCharacterRegression : K.fixedOrbitCount K.e ≡ 5
identityCharacterRegression = refl

halfTurnCharacterRegression : K.fixedOrbitCount K.r2 ≡ 5
halfTurnCharacterRegression = refl

quarterTurnCharacterRegression : K.fixedOrbitCount K.r ≡ 1
quarterTurnCharacterRegression = refl

axisReflectionCharacterRegression : K.fixedOrbitCount K.sAxis ≡ 3
axisReflectionCharacterRegression = refl

diagonalReflectionCharacterRegression : K.fixedOrbitCount K.sDiag ≡ 3
diagonalReflectionCharacterRegression = refl

quotientDecompositionA1Regression : K.quotientA1Multiplicity ≡ 3
quotientDecompositionA1Regression = refl

quotientDecompositionA2Regression : K.quotientA2Multiplicity ≡ 0
quotientDecompositionA2Regression = refl

quotientDecompositionB1Regression : K.quotientB1Multiplicity ≡ 1
quotientDecompositionB1Regression = refl

quotientDecompositionB2Regression : K.quotientB2Multiplicity ≡ 1
quotientDecompositionB2Regression = refl

quotientDecompositionERegression : K.quotientEMultiplicity ≡ 0
quotientDecompositionERegression = refl

characterReconstructionRegression :
  K.reconstructedCharacterVector ≡ K.quotientCharacterVector
characterReconstructionRegression = K.reconstructedCharacterIsQuotientCharacter

rawIdentityRegression : K.rawIdentity ≡ 9
rawIdentityRegression = refl

rawHalfTurnRegression : K.rawHalfTurn ≡ 1
rawHalfTurnRegression = refl

rawQuarterTurnRegression : K.rawQuarterTurn ≡ 1
rawQuarterTurnRegression = refl

rawAxisReflectionRegression : K.rawAxisReflection ≡ 3
rawAxisReflectionRegression = refl

rawDiagonalReflectionRegression : K.rawDiagonalReflection ≡ 3
rawDiagonalReflectionRegression = refl

removedEDimensionRegression : K.removedEDimension ≡ 4
removedEDimensionRegression = K.removedEDimensionIsFour
