module DASHI.Cognition.PNF.X369OriginalTorusSpectralBasisExact where

-- X369 A03/A04: exact original torus Fourier DELTA BASIS identities.
-- The mathematical carrier is the pre-existing
-- FiniteThreeCycleTorusExact.Torus3x3; Fourier.canonicalModes supplies
-- the original 9-frequency enumeration and TriadicDepthOneCharacters
-- supplies actual C3 symbolic character multiplication/conjugation.
--
-- Character-multiplicativity is proved with the original additive
-- carrier, not a second synthetic C3xC3. The direct 81+81+81
-- inversion / Parseval / reality cases are finite basis witnesses.
-- Universal full-functions convolution/Parseval distributivity,
-- real four-character-pair descent, and a kernel receipt remain OPEN.
-- No trained Leech, physical NS/YM, Monster, or continuum assertion.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; _+_; _*_; -_)

import DASHI.Physics.Common.FiniteThreeCycleTorusExact as Torus
import DASHI.Cognition.PNF.X369OriginalTorusGroupLawExact as Group
import DASHI.Biology.BalancedTernaryFourierModeExact as Fourier
import DASHI.Algebra.TriadicDepthOneCharacters as Characters
import DASHI.Algebra.TriadicFiniteArithmetic as Arithmetic
import DASHI.Cognition.PNF.X369OriginalTorusCharacterOrthogonalityExact as Orth

-- Explicit Z[omega] multiplication in Eisenstein integer pairs.
-- (a+bω)(c+dω)=(ac-bd)+(ad+bc-bd)ω, ω²+ω+1=0.
multiplyE : Orth.Eisenstein → Orth.Eisenstein → Orth.Eisenstein
multiplyE (Orth.eisenstein a b) (Orth.eisenstein c d) =
  Orth.eisenstein ((a * c) + (- (b * d)))
                  (((a * d) + (b * c)) + (- (b * d)))

conjugateE : Orth.Eisenstein → Orth.Eisenstein
conjugateE (Orth.eisenstein a b) =
  Orth.eisenstein (a + (- b)) (- b)

phaseProductToRing : (a b : Characters.C3Phase) →
  Orth.phaseE (Characters.multiplyPhase a b) ≡
  multiplyE (Orth.phaseE a) (Orth.phaseE b)
phaseProductToRing Characters.phase0 Characters.phase0 = refl
phaseProductToRing Characters.phase0 Characters.phase1 = refl
phaseProductToRing Characters.phase0 Characters.phase2 = refl
phaseProductToRing Characters.phase1 Characters.phase0 = refl
phaseProductToRing Characters.phase1 Characters.phase1 = refl
phaseProductToRing Characters.phase1 Characters.phase2 = refl
phaseProductToRing Characters.phase2 Characters.phase0 = refl
phaseProductToRing Characters.phase2 Characters.phase1 = refl
phaseProductToRing Characters.phase2 Characters.phase2 = refl

conjugatePhaseToRing : (a : Characters.C3Phase) →
  Orth.phaseE (Characters.conjugatePhase a) ≡
  conjugateE (Orth.phaseE a)
conjugatePhaseToRing Characters.phase0 = refl
conjugatePhaseToRing Characters.phase1 = refl
conjugatePhaseToRing Characters.phase2 = refl

conjugateProduct : (a b : Characters.C3Phase) →
  Characters.conjugatePhase (Characters.multiplyPhase a b) ≡
  Characters.multiplyPhase (Characters.conjugatePhase a)
                           (Characters.conjugatePhase b)
conjugateProduct Characters.phase0 Characters.phase0 = refl
conjugateProduct Characters.phase0 Characters.phase1 = refl
conjugateProduct Characters.phase0 Characters.phase2 = refl
conjugateProduct Characters.phase1 Characters.phase0 = refl
conjugateProduct Characters.phase1 Characters.phase1 = refl
conjugateProduct Characters.phase1 Characters.phase2 = refl
conjugateProduct Characters.phase2 Characters.phase0 = refl
conjugateProduct Characters.phase2 Characters.phase1 = refl
conjugateProduct Characters.phase2 Characters.phase2 = refl

encodeOriginalResidueAddition : (a b : Torus.Residue3) →
  Fourier.encodeResidue (Group.addResidue3 a b) ≡
  Arithmetic.addResidue (Fourier.encodeResidue a)
                        (Fourier.encodeResidue b)
encodeOriginalResidueAddition Torus.residueMinus Torus.residueMinus = refl
encodeOriginalResidueAddition Torus.residueMinus Torus.residueZero = refl
encodeOriginalResidueAddition Torus.residueMinus Torus.residuePlus = refl
encodeOriginalResidueAddition Torus.residueZero Torus.residueMinus = refl
encodeOriginalResidueAddition Torus.residueZero Torus.residueZero = refl
encodeOriginalResidueAddition Torus.residueZero Torus.residuePlus = refl
encodeOriginalResidueAddition Torus.residuePlus Torus.residueMinus = refl
encodeOriginalResidueAddition Torus.residuePlus Torus.residueZero = refl
encodeOriginalResidueAddition Torus.residuePlus Torus.residuePlus = refl


originalFirstCharacterAdd : (mode x y : Torus.Torus3x3) →
  Fourier.firstCharacter mode (Group.originalTorusAdd x y) ≡
  Characters.multiplyPhase (Fourier.firstCharacter mode x)
                           (Fourier.firstCharacter mode y)
originalFirstCharacterAdd (Torus.torusPoint m n)
  (Torus.torusPoint a b) (Torus.torusPoint c d)
  rewrite encodeOriginalResidueAddition a c =
  Characters.characterAdditive (Fourier.encodeResidue m)
    (Fourier.encodeResidue a) (Fourier.encodeResidue c)

originalSecondCharacterAdd : (mode x y : Torus.Torus3x3) →
  Fourier.secondCharacter mode (Group.originalTorusAdd x y) ≡
  Characters.multiplyPhase (Fourier.secondCharacter mode x)
                           (Fourier.secondCharacter mode y)
originalSecondCharacterAdd (Torus.torusPoint m n)
  (Torus.torusPoint a b) (Torus.torusPoint c d)
  rewrite encodeOriginalResidueAddition b d =
  Characters.characterAdditive (Fourier.encodeResidue n)
    (Fourier.encodeResidue b) (Fourier.encodeResidue d)

-- Reorder a c b d into a b c d in the actual original phase group.
phaseMiddleSwap : (a b c d : Characters.C3Phase) →
  Characters.multiplyPhase
    (Characters.multiplyPhase a c)
    (Characters.multiplyPhase b d) ≡
  Characters.multiplyPhase
    (Characters.multiplyPhase a b)
    (Characters.multiplyPhase c d)
phaseMiddleSwap Characters.phase0 Characters.phase0 Characters.phase0 Characters.phase0 = refl
phaseMiddleSwap Characters.phase0 Characters.phase0 Characters.phase0 Characters.phase1 = refl
phaseMiddleSwap Characters.phase0 Characters.phase0 Characters.phase0 Characters.phase2 = refl
phaseMiddleSwap Characters.phase0 Characters.phase0 Characters.phase1 Characters.phase0 = refl
phaseMiddleSwap Characters.phase0 Characters.phase0 Characters.phase1 Characters.phase1 = refl
phaseMiddleSwap Characters.phase0 Characters.phase0 Characters.phase1 Characters.phase2 = refl
phaseMiddleSwap Characters.phase0 Characters.phase0 Characters.phase2 Characters.phase0 = refl
phaseMiddleSwap Characters.phase0 Characters.phase0 Characters.phase2 Characters.phase1 = refl
phaseMiddleSwap Characters.phase0 Characters.phase0 Characters.phase2 Characters.phase2 = refl
phaseMiddleSwap Characters.phase0 Characters.phase1 Characters.phase0 Characters.phase0 = refl
phaseMiddleSwap Characters.phase0 Characters.phase1 Characters.phase0 Characters.phase1 = refl
phaseMiddleSwap Characters.phase0 Characters.phase1 Characters.phase0 Characters.phase2 = refl
phaseMiddleSwap Characters.phase0 Characters.phase1 Characters.phase1 Characters.phase0 = refl
phaseMiddleSwap Characters.phase0 Characters.phase1 Characters.phase1 Characters.phase1 = refl
phaseMiddleSwap Characters.phase0 Characters.phase1 Characters.phase1 Characters.phase2 = refl
phaseMiddleSwap Characters.phase0 Characters.phase1 Characters.phase2 Characters.phase0 = refl
phaseMiddleSwap Characters.phase0 Characters.phase1 Characters.phase2 Characters.phase1 = refl
phaseMiddleSwap Characters.phase0 Characters.phase1 Characters.phase2 Characters.phase2 = refl
phaseMiddleSwap Characters.phase0 Characters.phase2 Characters.phase0 Characters.phase0 = refl
phaseMiddleSwap Characters.phase0 Characters.phase2 Characters.phase0 Characters.phase1 = refl
phaseMiddleSwap Characters.phase0 Characters.phase2 Characters.phase0 Characters.phase2 = refl
phaseMiddleSwap Characters.phase0 Characters.phase2 Characters.phase1 Characters.phase0 = refl
phaseMiddleSwap Characters.phase0 Characters.phase2 Characters.phase1 Characters.phase1 = refl
phaseMiddleSwap Characters.phase0 Characters.phase2 Characters.phase1 Characters.phase2 = refl
phaseMiddleSwap Characters.phase0 Characters.phase2 Characters.phase2 Characters.phase0 = refl
phaseMiddleSwap Characters.phase0 Characters.phase2 Characters.phase2 Characters.phase1 = refl
phaseMiddleSwap Characters.phase0 Characters.phase2 Characters.phase2 Characters.phase2 = refl
phaseMiddleSwap Characters.phase1 Characters.phase0 Characters.phase0 Characters.phase0 = refl
phaseMiddleSwap Characters.phase1 Characters.phase0 Characters.phase0 Characters.phase1 = refl
phaseMiddleSwap Characters.phase1 Characters.phase0 Characters.phase0 Characters.phase2 = refl
phaseMiddleSwap Characters.phase1 Characters.phase0 Characters.phase1 Characters.phase0 = refl
phaseMiddleSwap Characters.phase1 Characters.phase0 Characters.phase1 Characters.phase1 = refl
phaseMiddleSwap Characters.phase1 Characters.phase0 Characters.phase1 Characters.phase2 = refl
phaseMiddleSwap Characters.phase1 Characters.phase0 Characters.phase2 Characters.phase0 = refl
phaseMiddleSwap Characters.phase1 Characters.phase0 Characters.phase2 Characters.phase1 = refl
phaseMiddleSwap Characters.phase1 Characters.phase0 Characters.phase2 Characters.phase2 = refl
phaseMiddleSwap Characters.phase1 Characters.phase1 Characters.phase0 Characters.phase0 = refl
phaseMiddleSwap Characters.phase1 Characters.phase1 Characters.phase0 Characters.phase1 = refl
phaseMiddleSwap Characters.phase1 Characters.phase1 Characters.phase0 Characters.phase2 = refl
phaseMiddleSwap Characters.phase1 Characters.phase1 Characters.phase1 Characters.phase0 = refl
phaseMiddleSwap Characters.phase1 Characters.phase1 Characters.phase1 Characters.phase1 = refl
phaseMiddleSwap Characters.phase1 Characters.phase1 Characters.phase1 Characters.phase2 = refl
phaseMiddleSwap Characters.phase1 Characters.phase1 Characters.phase2 Characters.phase0 = refl
phaseMiddleSwap Characters.phase1 Characters.phase1 Characters.phase2 Characters.phase1 = refl
phaseMiddleSwap Characters.phase1 Characters.phase1 Characters.phase2 Characters.phase2 = refl
phaseMiddleSwap Characters.phase1 Characters.phase2 Characters.phase0 Characters.phase0 = refl
phaseMiddleSwap Characters.phase1 Characters.phase2 Characters.phase0 Characters.phase1 = refl
phaseMiddleSwap Characters.phase1 Characters.phase2 Characters.phase0 Characters.phase2 = refl
phaseMiddleSwap Characters.phase1 Characters.phase2 Characters.phase1 Characters.phase0 = refl
phaseMiddleSwap Characters.phase1 Characters.phase2 Characters.phase1 Characters.phase1 = refl
phaseMiddleSwap Characters.phase1 Characters.phase2 Characters.phase1 Characters.phase2 = refl
phaseMiddleSwap Characters.phase1 Characters.phase2 Characters.phase2 Characters.phase0 = refl
phaseMiddleSwap Characters.phase1 Characters.phase2 Characters.phase2 Characters.phase1 = refl
phaseMiddleSwap Characters.phase1 Characters.phase2 Characters.phase2 Characters.phase2 = refl
phaseMiddleSwap Characters.phase2 Characters.phase0 Characters.phase0 Characters.phase0 = refl
phaseMiddleSwap Characters.phase2 Characters.phase0 Characters.phase0 Characters.phase1 = refl
phaseMiddleSwap Characters.phase2 Characters.phase0 Characters.phase0 Characters.phase2 = refl
phaseMiddleSwap Characters.phase2 Characters.phase0 Characters.phase1 Characters.phase0 = refl
phaseMiddleSwap Characters.phase2 Characters.phase0 Characters.phase1 Characters.phase1 = refl
phaseMiddleSwap Characters.phase2 Characters.phase0 Characters.phase1 Characters.phase2 = refl
phaseMiddleSwap Characters.phase2 Characters.phase0 Characters.phase2 Characters.phase0 = refl
phaseMiddleSwap Characters.phase2 Characters.phase0 Characters.phase2 Characters.phase1 = refl
phaseMiddleSwap Characters.phase2 Characters.phase0 Characters.phase2 Characters.phase2 = refl
phaseMiddleSwap Characters.phase2 Characters.phase1 Characters.phase0 Characters.phase0 = refl
phaseMiddleSwap Characters.phase2 Characters.phase1 Characters.phase0 Characters.phase1 = refl
phaseMiddleSwap Characters.phase2 Characters.phase1 Characters.phase0 Characters.phase2 = refl
phaseMiddleSwap Characters.phase2 Characters.phase1 Characters.phase1 Characters.phase0 = refl
phaseMiddleSwap Characters.phase2 Characters.phase1 Characters.phase1 Characters.phase1 = refl
phaseMiddleSwap Characters.phase2 Characters.phase1 Characters.phase1 Characters.phase2 = refl
phaseMiddleSwap Characters.phase2 Characters.phase1 Characters.phase2 Characters.phase0 = refl
phaseMiddleSwap Characters.phase2 Characters.phase1 Characters.phase2 Characters.phase1 = refl
phaseMiddleSwap Characters.phase2 Characters.phase1 Characters.phase2 Characters.phase2 = refl
phaseMiddleSwap Characters.phase2 Characters.phase2 Characters.phase0 Characters.phase0 = refl
phaseMiddleSwap Characters.phase2 Characters.phase2 Characters.phase0 Characters.phase1 = refl
phaseMiddleSwap Characters.phase2 Characters.phase2 Characters.phase0 Characters.phase2 = refl
phaseMiddleSwap Characters.phase2 Characters.phase2 Characters.phase1 Characters.phase0 = refl
phaseMiddleSwap Characters.phase2 Characters.phase2 Characters.phase1 Characters.phase1 = refl
phaseMiddleSwap Characters.phase2 Characters.phase2 Characters.phase1 Characters.phase2 = refl
phaseMiddleSwap Characters.phase2 Characters.phase2 Characters.phase2 Characters.phase0 = refl
phaseMiddleSwap Characters.phase2 Characters.phase2 Characters.phase2 Characters.phase1 = refl
phaseMiddleSwap Characters.phase2 Characters.phase2 Characters.phase2 Characters.phase2 = refl


originalCombinedCharacterAdd : (mode x y : Torus.Torus3x3) →
  Orth.combinedCharacter mode (Group.originalTorusAdd x y) ≡
  Characters.multiplyPhase (Orth.combinedCharacter mode x)
                           (Orth.combinedCharacter mode y)
originalCombinedCharacterAdd mode x y
  rewrite originalFirstCharacterAdd mode x y
        | originalSecondCharacterAdd mode x y =
  phaseMiddleSwap (Fourier.firstCharacter mode x)
                  (Fourier.secondCharacter mode x)
                  (Fourier.firstCharacter mode y)
                  (Fourier.secondCharacter mode y)

-- The UNNORMALISED Fourier transform of the delta at site u.
originalDeltaFourier : Torus.Torus3x3 → Torus.Torus3x3 →
                       Orth.Eisenstein
originalDeltaFourier site frequency =
  Orth.phaseE (Characters.conjugatePhase
    (Orth.combinedCharacter frequency site))

originalDeltaFourierConvolutionCoefficient :
  (a b mode : Torus.Torus3x3) →
  originalDeltaFourier (Group.originalTorusAdd a b) mode ≡
  multiplyE (originalDeltaFourier a mode)
            (originalDeltaFourier b mode)
originalDeltaFourierConvolutionCoefficient a b mode
  rewrite originalCombinedCharacterAdd mode a b
        | conjugateProduct (Orth.combinedCharacter mode a)
                           (Orth.combinedCharacter mode b)
        | phaseProductToRing
            (Characters.conjugatePhase (Orth.combinedCharacter mode a))
            (Characters.conjugatePhase (Orth.combinedCharacter mode b))
  = refl

-- Correct FT inverse scaling is N=9. This statement is precisely the
-- 81 matrix coefficients, not just an appeal to "Fourier inversion".
originalInverseCoefficient : Torus.Torus3x3 → Torus.Torus3x3 →
                             Orth.Eisenstein
originalInverseCoefficient x y =
  Orth.sumFiniteOriginalTorus
    (λ mode → multiplyE
      (Orth.phaseE (Orth.combinedCharacter mode x))
      (originalDeltaFourier y mode))
    Fourier.canonicalModes

originalDualInverseCoefficient :
  (x y : Torus.Torus3x3) →
  originalInverseCoefficient x y ≡
  Orth.diagonalTarget (Orth.sameOriginalPoint x y)
originalDualInverseCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueMinus) (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueMinus) (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueMinus) (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueMinus) (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueMinus) (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueMinus) (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueMinus) (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueMinus) (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueMinus) (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueZero) (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueZero) (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueZero) (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueZero) (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueZero) (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueZero) (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueZero) (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueZero) (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueZero) (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueMinus Torus.residuePlus) (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueMinus Torus.residuePlus) (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueMinus Torus.residuePlus) (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueMinus Torus.residuePlus) (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueMinus Torus.residuePlus) (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueMinus Torus.residuePlus) (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueMinus Torus.residuePlus) (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueMinus Torus.residuePlus) (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueMinus Torus.residuePlus) (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueZero Torus.residueMinus) (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueZero Torus.residueMinus) (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueZero Torus.residueMinus) (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueZero Torus.residueMinus) (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueZero Torus.residueMinus) (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueZero Torus.residueMinus) (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueZero Torus.residueMinus) (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueZero Torus.residueMinus) (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueZero Torus.residueMinus) (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueZero Torus.residueZero) (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueZero Torus.residueZero) (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueZero Torus.residueZero) (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueZero Torus.residueZero) (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueZero Torus.residueZero) (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueZero Torus.residueZero) (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueZero Torus.residueZero) (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueZero Torus.residueZero) (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueZero Torus.residueZero) (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueZero Torus.residuePlus) (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueZero Torus.residuePlus) (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueZero Torus.residuePlus) (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueZero Torus.residuePlus) (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueZero Torus.residuePlus) (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueZero Torus.residuePlus) (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueZero Torus.residuePlus) (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueZero Torus.residuePlus) (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residueZero Torus.residuePlus) (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueMinus) (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueMinus) (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueMinus) (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueMinus) (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueMinus) (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueMinus) (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueMinus) (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueMinus) (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueMinus) (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueZero) (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueZero) (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueZero) (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueZero) (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueZero) (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueZero) (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueZero) (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueZero) (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueZero) (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residuePlus Torus.residuePlus) (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residuePlus Torus.residuePlus) (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residuePlus Torus.residuePlus) (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residuePlus Torus.residuePlus) (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residuePlus Torus.residuePlus) (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residuePlus Torus.residuePlus) (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residuePlus Torus.residuePlus) (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residuePlus Torus.residuePlus) (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalDualInverseCoefficient (Torus.torusPoint Torus.residuePlus Torus.residuePlus) (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl


-- Orthogonal delta basis: for an arbitrary *complex* pair of fields
-- the remaining general theorem needs the finite bilinear sum fold.
originalParsevalCoefficient : Torus.Torus3x3 → Torus.Torus3x3 →
                              Orth.Eisenstein
originalParsevalCoefficient x y =
  Orth.sumFiniteOriginalTorus
    (λ mode → multiplyE (originalDeltaFourier x mode)
                        (conjugateE (originalDeltaFourier y mode)))
    Fourier.canonicalModes

originalParsevalBasisCoefficient :
  (x y : Torus.Torus3x3) →
  originalParsevalCoefficient x y ≡
  Orth.diagonalTarget (Orth.sameOriginalPoint x y)
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueMinus) (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueMinus) (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueMinus) (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueMinus) (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueMinus) (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueMinus) (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueMinus) (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueMinus) (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueMinus) (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueZero) (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueZero) (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueZero) (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueZero) (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueZero) (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueZero) (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueZero) (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueZero) (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueMinus Torus.residueZero) (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueMinus Torus.residuePlus) (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueMinus Torus.residuePlus) (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueMinus Torus.residuePlus) (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueMinus Torus.residuePlus) (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueMinus Torus.residuePlus) (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueMinus Torus.residuePlus) (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueMinus Torus.residuePlus) (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueMinus Torus.residuePlus) (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueMinus Torus.residuePlus) (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueZero Torus.residueMinus) (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueZero Torus.residueMinus) (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueZero Torus.residueMinus) (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueZero Torus.residueMinus) (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueZero Torus.residueMinus) (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueZero Torus.residueMinus) (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueZero Torus.residueMinus) (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueZero Torus.residueMinus) (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueZero Torus.residueMinus) (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueZero Torus.residueZero) (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueZero Torus.residueZero) (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueZero Torus.residueZero) (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueZero Torus.residueZero) (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueZero Torus.residueZero) (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueZero Torus.residueZero) (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueZero Torus.residueZero) (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueZero Torus.residueZero) (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueZero Torus.residueZero) (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueZero Torus.residuePlus) (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueZero Torus.residuePlus) (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueZero Torus.residuePlus) (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueZero Torus.residuePlus) (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueZero Torus.residuePlus) (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueZero Torus.residuePlus) (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueZero Torus.residuePlus) (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueZero Torus.residuePlus) (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residueZero Torus.residuePlus) (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueMinus) (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueMinus) (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueMinus) (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueMinus) (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueMinus) (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueMinus) (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueMinus) (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueMinus) (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueMinus) (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueZero) (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueZero) (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueZero) (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueZero) (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueZero) (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueZero) (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueZero) (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueZero) (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residuePlus Torus.residueZero) (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residuePlus Torus.residuePlus) (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residuePlus Torus.residuePlus) (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residuePlus Torus.residuePlus) (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residuePlus Torus.residuePlus) (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residuePlus Torus.residuePlus) (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residuePlus Torus.residuePlus) (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residuePlus Torus.residuePlus) (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residuePlus Torus.residuePlus) (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalParsevalBasisCoefficient (Torus.torusPoint Torus.residuePlus Torus.residuePlus) (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl


originalRealConjugationBasis :
  (site mode : Torus.Torus3x3) →
  originalDeltaFourier site (Group.originalTorusInverse mode) ≡
  conjugateE (originalDeltaFourier site mode)
originalRealConjugationBasis (Torus.torusPoint Torus.residueMinus Torus.residueMinus) (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueMinus Torus.residueMinus) (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueMinus Torus.residueMinus) (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueMinus Torus.residueMinus) (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueMinus Torus.residueMinus) (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueMinus Torus.residueMinus) (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueMinus Torus.residueMinus) (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueMinus Torus.residueMinus) (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueMinus Torus.residueMinus) (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueMinus Torus.residueZero) (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueMinus Torus.residueZero) (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueMinus Torus.residueZero) (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueMinus Torus.residueZero) (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueMinus Torus.residueZero) (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueMinus Torus.residueZero) (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueMinus Torus.residueZero) (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueMinus Torus.residueZero) (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueMinus Torus.residueZero) (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueMinus Torus.residuePlus) (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueMinus Torus.residuePlus) (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueMinus Torus.residuePlus) (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueMinus Torus.residuePlus) (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueMinus Torus.residuePlus) (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueMinus Torus.residuePlus) (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueMinus Torus.residuePlus) (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueMinus Torus.residuePlus) (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueMinus Torus.residuePlus) (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueZero Torus.residueMinus) (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueZero Torus.residueMinus) (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueZero Torus.residueMinus) (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueZero Torus.residueMinus) (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueZero Torus.residueMinus) (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueZero Torus.residueMinus) (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueZero Torus.residueMinus) (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueZero Torus.residueMinus) (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueZero Torus.residueMinus) (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueZero Torus.residueZero) (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueZero Torus.residueZero) (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueZero Torus.residueZero) (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueZero Torus.residueZero) (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueZero Torus.residueZero) (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueZero Torus.residueZero) (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueZero Torus.residueZero) (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueZero Torus.residueZero) (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueZero Torus.residueZero) (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueZero Torus.residuePlus) (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueZero Torus.residuePlus) (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueZero Torus.residuePlus) (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueZero Torus.residuePlus) (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueZero Torus.residuePlus) (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueZero Torus.residuePlus) (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueZero Torus.residuePlus) (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueZero Torus.residuePlus) (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residueZero Torus.residuePlus) (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residuePlus Torus.residueMinus) (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residuePlus Torus.residueMinus) (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residuePlus Torus.residueMinus) (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residuePlus Torus.residueMinus) (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residuePlus Torus.residueMinus) (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residuePlus Torus.residueMinus) (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residuePlus Torus.residueMinus) (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residuePlus Torus.residueMinus) (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residuePlus Torus.residueMinus) (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residuePlus Torus.residueZero) (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residuePlus Torus.residueZero) (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residuePlus Torus.residueZero) (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residuePlus Torus.residueZero) (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residuePlus Torus.residueZero) (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residuePlus Torus.residueZero) (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residuePlus Torus.residueZero) (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residuePlus Torus.residueZero) (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residuePlus Torus.residueZero) (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residuePlus Torus.residuePlus) (Torus.torusPoint Torus.residueMinus Torus.residueMinus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residuePlus Torus.residuePlus) (Torus.torusPoint Torus.residueMinus Torus.residueZero) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residuePlus Torus.residuePlus) (Torus.torusPoint Torus.residueMinus Torus.residuePlus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residuePlus Torus.residuePlus) (Torus.torusPoint Torus.residueZero Torus.residueMinus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residuePlus Torus.residuePlus) (Torus.torusPoint Torus.residueZero Torus.residueZero) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residuePlus Torus.residuePlus) (Torus.torusPoint Torus.residueZero Torus.residuePlus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residuePlus Torus.residuePlus) (Torus.torusPoint Torus.residuePlus Torus.residueMinus) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residuePlus Torus.residuePlus) (Torus.torusPoint Torus.residuePlus Torus.residueZero) = refl
originalRealConjugationBasis (Torus.torusPoint Torus.residuePlus Torus.residuePlus) (Torus.torusPoint Torus.residuePlus Torus.residuePlus) = refl


-- Next proofs: nine-site function linear extension, convolution of
-- arbitrary same-carrier fields, full conjugate-linear Parseval, real
-- zero-mean puncture wave/centre BIDI, original Python source SHA audit.
