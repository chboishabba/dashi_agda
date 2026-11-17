module DASHI.Biology.BalancedTernaryFourierModeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- Ingrid Daubechies,
-- "Ten Lectures on Wavelets", SIAM, 1992.
-- DOI: 10.1137/1.9781611970104.
--
-- DASHI CONTRIBUTION
--
-- Turn the existing finite 3 x 3 balanced-ternary torus into an exact
-- translation-mode carrier.  Each coordinate frequency is the already-proved
-- additive character of Z/3Z.  Translation by one ternary step multiplies the
-- matching coordinate character by its exact symbolic third-root eigenphase,
-- while the orthogonal coordinate character is unchanged.
--
-- The two coordinate characters therefore form a joint finite Fourier-mode
-- label for T^2_3.  Pairing the nine coarse labels with the existing 3^9
-- fine-frequency fibre gives the exact 3^11 ordinary harmonic count.  The
-- completed j channel remains fixed by both translations, so evaluation at j
-- is exactly translation invariant.
--
-- This is finite-group harmonic analysis.  It does not assert a continuum
-- Fourier transform, physical wavelength, cortical geometry, or Monster action.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_*_)
open import Data.Product using (_×_)

import DASHI.Algebra.TriadicDepthOneCharacters as Characters
import DASHI.Foundations.TriadicFiniteQuotient as Quotient
import DASHI.Algebra.TriadicFiniteArithmetic as Arithmetic
import DASHI.Physics.Common.FiniteThreeCycleTorusExact as Torus
import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic

open Characters using
  ( C3Phase; phase0; phase1; phase2; multiplyPhase
  ; rNeg; rZero; rPos; characterValue; characterAdditive
  )

encodeResidue : Torus.Residue3 → Quotient.Residue3Pow Quotient.one
encodeResidue Torus.residueMinus = rNeg
encodeResidue Torus.residueZero = rZero
encodeResidue Torus.residuePlus = rPos

encodeNext : ∀ residue →
  encodeResidue (Torus.next3 residue)
  ≡ Arithmetic.addResidue (encodeResidue residue) rPos
encodeNext Torus.residueMinus = refl
encodeNext Torus.residueZero = refl
encodeNext Torus.residuePlus = refl

Mode3x3 : Set
Mode3x3 = Torus.Torus3x3

firstCharacter : Mode3x3 → Torus.Torus3x3 → C3Phase
firstCharacter mode point =
  characterValue
    (encodeResidue (Torus.firstCoordinate mode))
    (encodeResidue (Torus.firstCoordinate point))

secondCharacter : Mode3x3 → Torus.Torus3x3 → C3Phase
secondCharacter mode point =
  characterValue
    (encodeResidue (Torus.secondCoordinate mode))
    (encodeResidue (Torus.secondCoordinate point))

firstEigenphase : Mode3x3 → C3Phase
firstEigenphase mode =
  characterValue
    (encodeResidue (Torus.firstCoordinate mode))
    rPos

secondEigenphase : Mode3x3 → C3Phase
secondEigenphase mode =
  characterValue
    (encodeResidue (Torus.secondCoordinate mode))
    rPos

firstTranslationEigen : ∀ mode point →
  firstCharacter mode (Torus.translateFirst point)
  ≡ multiplyPhase (firstCharacter mode point) (firstEigenphase mode)
firstTranslationEigen
    (Torus.torusPoint m n)
    (Torus.torusPoint x y)
  rewrite encodeNext x =
    characterAdditive (encodeResidue m) (encodeResidue x) rPos

secondTranslationEigen : ∀ mode point →
  secondCharacter mode (Torus.translateSecond point)
  ≡ multiplyPhase (secondCharacter mode point) (secondEigenphase mode)
secondTranslationEigen
    (Torus.torusPoint m n)
    (Torus.torusPoint x y)
  rewrite encodeNext y =
    characterAdditive (encodeResidue n) (encodeResidue y) rPos

firstCharacterIgnoresSecondTranslation : ∀ mode point →
  firstCharacter mode (Torus.translateSecond point)
  ≡ firstCharacter mode point
firstCharacterIgnoresSecondTranslation mode (Torus.torusPoint x y) = refl

secondCharacterIgnoresFirstTranslation : ∀ mode point →
  secondCharacter mode (Torus.translateFirst point)
  ≡ secondCharacter mode point
secondCharacterIgnoresFirstTranslation mode (Torus.torusPoint x y) = refl

canonicalModes : List Mode3x3
canonicalModes =
  Torus.torusPoint Torus.residueMinus Torus.residueMinus ∷
  Torus.torusPoint Torus.residueMinus Torus.residueZero ∷
  Torus.torusPoint Torus.residueMinus Torus.residuePlus ∷
  Torus.torusPoint Torus.residueZero Torus.residueMinus ∷
  Torus.torusPoint Torus.residueZero Torus.residueZero ∷
  Torus.torusPoint Torus.residueZero Torus.residuePlus ∷
  Torus.torusPoint Torus.residuePlus Torus.residueMinus ∷
  Torus.torusPoint Torus.residuePlus Torus.residueZero ∷
  Torus.torusPoint Torus.residuePlus Torus.residuePlus ∷
  []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

canonicalModeCountIsNine : listCount canonicalModes ≡ 9
canonicalModeCountIsNine = refl

SymmetryResolvedFineMode : Set
SymmetryResolvedFineMode = Mode3x3 × Harmonic.FineFrequency

coarseModeDimension : Nat
coarseModeDimension = 9

fineModeDimension : Nat
fineModeDimension = Harmonic.fineFrequencyDimension

ordinarySymmetryResolvedDimension : Nat
ordinarySymmetryResolvedDimension = coarseModeDimension * fineModeDimension

ordinarySymmetryResolvedDimensionIsThreePowerEleven :
  ordinarySymmetryResolvedDimension ≡ 177147
ordinarySymmetryResolvedDimensionIsThreePowerEleven = refl

completionReadout : ∀ {State : Set} → Torus.Field State → State
completionReadout field = field Torus.completionChannel

completionReadoutFirstInvariant :
  ∀ {State : Set} (field : Torus.Field State) →
  completionReadout (Torus.pullbackFirst field) ≡ completionReadout field
completionReadoutFirstInvariant field = refl

completionReadoutSecondInvariant :
  ∀ {State : Set} (field : Torus.Field State) →
  completionReadout (Torus.pullbackSecond field) ≡ completionReadout field
completionReadoutSecondInvariant field = refl

record FourierModeBoundary : Set where
  constructor fourierModeBoundary
  field
    finiteCharactersAreContinuumWaveNumbers : Set
    finiteCharactersAreNotContinuumWaveNumbers :
      finiteCharactersAreContinuumWaveNumbers → Set

    completionReadoutIsConsciousness : Set
    completionReadoutIsNotConsciousness :
      completionReadoutIsConsciousness → Set

    finiteModesConstructMonsterAction : Set
    finiteModesDoNotConstructMonsterAction :
      finiteModesConstructMonsterAction → Set

canonicalFourierModeBoundary : FourierModeBoundary
canonicalFourierModeBoundary =
  fourierModeBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
