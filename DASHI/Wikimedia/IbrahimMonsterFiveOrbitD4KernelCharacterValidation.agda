module DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4KernelCharacterValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

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

quotientCharacterRegression : K.quotientCharacterVector ≡ (5 K.∷ₙ 5 K.∷ₙ 1 K.∷ₙ 3 K.∷ₙ 3 K.∷ₙ K.[]ₙ)
quotientCharacterRegression = refl

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

characterReconstructionRegression : K.reconstructedCharacterVector ≡ K.quotientCharacterVector
characterReconstructionRegression = refl

removedERawNineRegression : K.rawNineCharacterVector ≡ (9 K.∷ₙ 1 K.∷ₙ 1 K.∷ₙ 3 K.∷ₙ 3 K.∷ₙ K.[]ₙ)
removedERawNineRegression = refl
