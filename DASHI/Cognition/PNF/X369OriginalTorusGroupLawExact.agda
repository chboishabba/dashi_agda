module DASHI.Cognition.PNF.X369OriginalTorusGroupLawExact where

-- Original-carrier group law: NOT a second synthetic nine-element torus.
-- Source: DASHI/Physics/Common/FiniteThreeCycleTorusExact.agda.
-- Audrey Terras, Fourier Analysis on Finite Groups and Applications
-- (1999), DOI 10.1017/CBO9780511626265.
-- Exact finite translation is a DASHI algebraic extension, not a
-- continuum-torus, neural E8, Monster, atomic, NS or Yang-Mills result.

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Common.FiniteThreeCycleTorusExact as Torus

addResidue3 : Torus.Residue3 → Torus.Residue3 → Torus.Residue3
addResidue3 x Torus.residueMinus = Torus.next3 (Torus.next3 x)
addResidue3 x Torus.residueZero = x
addResidue3 x Torus.residuePlus = Torus.next3 x

inverseResidue3 : Torus.Residue3 → Torus.Residue3
inverseResidue3 Torus.residueMinus = Torus.residuePlus
inverseResidue3 Torus.residueZero = Torus.residueZero
inverseResidue3 Torus.residuePlus = Torus.residueMinus

residueAddAssociative :
  ∀ a b c → addResidue3 (addResidue3 a b) c
          ≡ addResidue3 a (addResidue3 b c)
residueAddAssociative Torus.residueMinus Torus.residueMinus Torus.residueMinus = refl
residueAddAssociative Torus.residueMinus Torus.residueMinus Torus.residueZero = refl
residueAddAssociative Torus.residueMinus Torus.residueMinus Torus.residuePlus = refl
residueAddAssociative Torus.residueMinus Torus.residueZero Torus.residueMinus = refl
residueAddAssociative Torus.residueMinus Torus.residueZero Torus.residueZero = refl
residueAddAssociative Torus.residueMinus Torus.residueZero Torus.residuePlus = refl
residueAddAssociative Torus.residueMinus Torus.residuePlus Torus.residueMinus = refl
residueAddAssociative Torus.residueMinus Torus.residuePlus Torus.residueZero = refl
residueAddAssociative Torus.residueMinus Torus.residuePlus Torus.residuePlus = refl
residueAddAssociative Torus.residueZero Torus.residueMinus Torus.residueMinus = refl
residueAddAssociative Torus.residueZero Torus.residueMinus Torus.residueZero = refl
residueAddAssociative Torus.residueZero Torus.residueMinus Torus.residuePlus = refl
residueAddAssociative Torus.residueZero Torus.residueZero Torus.residueMinus = refl
residueAddAssociative Torus.residueZero Torus.residueZero Torus.residueZero = refl
residueAddAssociative Torus.residueZero Torus.residueZero Torus.residuePlus = refl
residueAddAssociative Torus.residueZero Torus.residuePlus Torus.residueMinus = refl
residueAddAssociative Torus.residueZero Torus.residuePlus Torus.residueZero = refl
residueAddAssociative Torus.residueZero Torus.residuePlus Torus.residuePlus = refl
residueAddAssociative Torus.residuePlus Torus.residueMinus Torus.residueMinus = refl
residueAddAssociative Torus.residuePlus Torus.residueMinus Torus.residueZero = refl
residueAddAssociative Torus.residuePlus Torus.residueMinus Torus.residuePlus = refl
residueAddAssociative Torus.residuePlus Torus.residueZero Torus.residueMinus = refl
residueAddAssociative Torus.residuePlus Torus.residueZero Torus.residueZero = refl
residueAddAssociative Torus.residuePlus Torus.residueZero Torus.residuePlus = refl
residueAddAssociative Torus.residuePlus Torus.residuePlus Torus.residueMinus = refl
residueAddAssociative Torus.residuePlus Torus.residuePlus Torus.residueZero = refl
residueAddAssociative Torus.residuePlus Torus.residuePlus Torus.residuePlus = refl

residueAddCommutative : ∀ a b →
  addResidue3 a b ≡ addResidue3 b a
residueAddCommutative Torus.residueMinus Torus.residueMinus = refl
residueAddCommutative Torus.residueMinus Torus.residueZero = refl
residueAddCommutative Torus.residueMinus Torus.residuePlus = refl
residueAddCommutative Torus.residueZero Torus.residueMinus = refl
residueAddCommutative Torus.residueZero Torus.residueZero = refl
residueAddCommutative Torus.residueZero Torus.residuePlus = refl
residueAddCommutative Torus.residuePlus Torus.residueMinus = refl
residueAddCommutative Torus.residuePlus Torus.residueZero = refl
residueAddCommutative Torus.residuePlus Torus.residuePlus = refl

residueAddLeftZero : ∀ a →
  addResidue3 Torus.residueZero a ≡ a
residueAddLeftZero Torus.residueMinus = refl
residueAddLeftZero Torus.residueZero = refl
residueAddLeftZero Torus.residuePlus = refl

residueAddRightZero : ∀ a →
  addResidue3 a Torus.residueZero ≡ a
residueAddRightZero a = refl

residueAddInverseRight : ∀ a →
  addResidue3 a (inverseResidue3 a) ≡ Torus.residueZero
residueAddInverseRight Torus.residueMinus = refl
residueAddInverseRight Torus.residueZero = refl
residueAddInverseRight Torus.residuePlus = refl

residueAddInverseLeft : ∀ a →
  addResidue3 (inverseResidue3 a) a ≡ Torus.residueZero
residueAddInverseLeft Torus.residueMinus = refl
residueAddInverseLeft Torus.residueZero = refl
residueAddInverseLeft Torus.residuePlus = refl

originalTorusZero : Torus.Torus3x3
originalTorusZero =
  Torus.torusPoint Torus.residueZero Torus.residueZero

originalTorusAdd : Torus.Torus3x3 → Torus.Torus3x3 → Torus.Torus3x3
originalTorusAdd (Torus.torusPoint a b) (Torus.torusPoint c d) =
  Torus.torusPoint (addResidue3 a c) (addResidue3 b d)

originalTorusInverse : Torus.Torus3x3 → Torus.Torus3x3
originalTorusInverse (Torus.torusPoint a b) =
  Torus.torusPoint (inverseResidue3 a) (inverseResidue3 b)

originalTorusAddAssociative :
  ∀ a b c →
  originalTorusAdd (originalTorusAdd a b) c
  ≡ originalTorusAdd a (originalTorusAdd b c)
originalTorusAddAssociative
    (Torus.torusPoint a b)
    (Torus.torusPoint c d)
    (Torus.torusPoint e f)
  rewrite residueAddAssociative a c e
        | residueAddAssociative b d f = refl

originalTorusAddCommutative :
  ∀ a b → originalTorusAdd a b ≡ originalTorusAdd b a
originalTorusAddCommutative
    (Torus.torusPoint a b) (Torus.torusPoint c d)
  rewrite residueAddCommutative a c
        | residueAddCommutative b d = refl

originalTorusLeftZero :
  ∀ a → originalTorusAdd originalTorusZero a ≡ a
originalTorusLeftZero (Torus.torusPoint a b)
  rewrite residueAddLeftZero a | residueAddLeftZero b = refl

originalTorusRightZero :
  ∀ a → originalTorusAdd a originalTorusZero ≡ a
originalTorusRightZero (Torus.torusPoint a b) = refl

originalTorusInverseRight :
  ∀ a → originalTorusAdd a (originalTorusInverse a) ≡ originalTorusZero
originalTorusInverseRight (Torus.torusPoint a b)
  rewrite residueAddInverseRight a | residueAddInverseRight b = refl

originalTorusInverseLeft :
  ∀ a → originalTorusAdd (originalTorusInverse a) a ≡ originalTorusZero
originalTorusInverseLeft (Torus.torusPoint a b)
  rewrite residueAddInverseLeft a | residueAddInverseLeft b = refl

originalTorusFirstGenerator : Torus.Torus3x3
originalTorusFirstGenerator =
  Torus.torusPoint Torus.residuePlus Torus.residueZero

originalTorusSecondGenerator : Torus.Torus3x3
originalTorusSecondGenerator =
  Torus.torusPoint Torus.residueZero Torus.residuePlus

firstGeneratorIsOriginalTranslation :
  ∀ point →
  originalTorusAdd point originalTorusFirstGenerator
  ≡ Torus.translateFirst point
firstGeneratorIsOriginalTranslation (Torus.torusPoint a b) = refl

secondGeneratorIsOriginalTranslation :
  ∀ point →
  originalTorusAdd point originalTorusSecondGenerator
  ≡ Torus.translateSecond point
secondGeneratorIsOriginalTranslation (Torus.torusPoint a b) = refl

-- A03 convolution/normalisation on this original group and A05 the
-- independent puncture centre-state transport are separate proof gates.
