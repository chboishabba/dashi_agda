module DASHI.Physics.Closure.NSTriadKNLuoTorusTrigonometricPolynomialExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphaël Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Loukas Grafakos.
-- Title: "Classical Fourier Analysis".
-- DOI: 10.1007/978-1-4939-1194-3.
--
-- PURPOSE
-- Define finite trigonometric polynomials directly on a torus-character
-- carrier and derive coefficient extraction from linearity and character
-- orthogonality.  The proof is an induction over the actual finite term list:
-- no finite cyclic root is used as a proxy for the continuum torus.
--
-- Construction of normalized Haar measure and the concrete exponential
-- character remain the analytic realization data.  Once supplied, the theorem
-- below gives the exact physical coefficient extractor used by the Galerkin
-- lane.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≢_; cong; cong₂; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring

kroneckerComplex :
  ∀ {r} {F : C3.RealField r} {Mode : Set} →
  ((left right : Mode) → Dec (left ≡ right)) →
  Mode → Mode → C3.Complex F
kroneckerComplex {F = F} decide left right with decide left right
... | yes _ = C3.complexOne F
... | no _ = C3.complexZero F

record TorusCharacterIntegral
    {r : Level}
    (F : C3.RealField r) : Set (lsuc r) where
  field
    Point Mode : Set

    decideModeEquality :
      (left right : Mode) → Dec (left ≡ right)

    integral :
      (Point → C3.Complex F) → C3.Complex F

    integralCong :
      ∀ {f g : Point → C3.Complex F} →
      (∀ point → f point ≡ g point) →
      integral f ≡ integral g

    integralZero :
      integral (λ _ → C3.complexZero F) ≡ C3.complexZero F

    integralAdd :
      (f g : Point → C3.Complex F) →
      integral (λ point → C3.complexAdd (f point) (g point))
      ≡ C3.complexAdd (integral f) (integral g)

    integralScale :
      (scalar : C3.Complex F) →
      (f : Point → C3.Complex F) →
      integral (λ point → C3.complexMultiply scalar (f point))
      ≡ C3.complexMultiply scalar (integral f)

    character :
      Mode → Point → C3.Complex F

    zeroMode : Mode

    characterProduct :
      Mode → Mode → Point → C3.Complex F

    conjugateCharacter :
      Mode → Point → C3.Complex F

    characterMultiply :
      (left right : Mode) →
      (point : Point) →
      C3.complexMultiply
        (character left point)
        (character right point)
      ≡ characterProduct left right point

    characterZero :
      (point : Point) →
      character zeroMode point ≡ C3.complexOne F

    characterConjugate :
      (mode : Mode) →
      (point : Point) →
      C3.complexConjugate (character mode point)
      ≡ conjugateCharacter mode point

    orthogonality :
      (left right : Mode) →
      integral
        (λ point →
          C3.complexMultiply
            (character left point)
            (conjugateCharacter right point))
      ≡ kroneckerComplex decideModeEquality left right

open TorusCharacterIntegral public

record TorusTerm
    {r : Level}
    (F : C3.RealField r)
    (Mode : Set) : Set r where
  constructor torus-term
  field
    mode : Mode
    coefficient : C3.Complex F

open TorusTerm public

termValue :
  ∀ {r} {F : C3.RealField r}
    (dataSet : TorusCharacterIntegral F) →
  TorusTerm F (Mode dataSet) →
  Point dataSet →
  C3.Complex F
termValue dataSet oneTerm point =
  C3.complexMultiply
    (coefficient oneTerm)
    (character dataSet (mode oneTerm) point)

polynomialValue :
  ∀ {r} {F : C3.RealField r}
    (dataSet : TorusCharacterIntegral F) →
  List (TorusTerm F (Mode dataSet)) →
  Point dataSet →
  C3.Complex F
polynomialValue dataSet [] point = C3.complexZero _
polynomialValue dataSet (oneTerm ∷ terms) point =
  C3.complexAdd
    (termValue dataSet oneTerm point)
    (polynomialValue dataSet terms point)

selectedTermCoefficient :
  ∀ {r} {F : C3.RealField r}
    (dataSet : TorusCharacterIntegral F) →
  TorusTerm F (Mode dataSet) →
  Mode dataSet →
  C3.Complex F
selectedTermCoefficient dataSet oneTerm target
  with decideModeEquality dataSet (mode oneTerm) target
... | yes _ = coefficient oneTerm
... | no _ = C3.complexZero _

selectedCoefficient :
  ∀ {r} {F : C3.RealField r}
    (dataSet : TorusCharacterIntegral F) →
  List (TorusTerm F (Mode dataSet)) →
  Mode dataSet →
  C3.Complex F
selectedCoefficient dataSet [] target = C3.complexZero _
selectedCoefficient dataSet (oneTerm ∷ terms) target =
  C3.complexAdd
    (selectedTermCoefficient dataSet oneTerm target)
    (selectedCoefficient dataSet terms target)

coefficientIntegral :
  ∀ {r} {F : C3.RealField r}
    (dataSet : TorusCharacterIntegral F) →
  List (TorusTerm F (Mode dataSet)) →
  Mode dataSet →
  C3.Complex F
coefficientIntegral dataSet terms target =
  integral dataSet
    (λ point →
      C3.complexMultiply
        (polynomialValue dataSet terms point)
        (conjugateCharacter dataSet target point))

complexMultiplyOneRight :
  ∀ {r} {F : C3.RealField r}
    (value : C3.Complex F) →
  C3.complexMultiply value (C3.complexOne F) ≡ value
complexMultiplyOneRight value =
  trans
    (Algebra.complexMultiplyCommutative value (C3.complexOne _))
    (Algebra.complexOneMultiply value)

singleTermCoefficientExtraction :
  ∀ {r} {F : C3.RealField r}
    (dataSet : TorusCharacterIntegral F)
    (oneTerm : TorusTerm F (Mode dataSet))
    (target : Mode dataSet) →
  integral dataSet
    (λ point →
      C3.complexMultiply
        (termValue dataSet oneTerm point)
        (conjugateCharacter dataSet target point))
  ≡ selectedTermCoefficient dataSet oneTerm target
singleTermCoefficientExtraction dataSet oneTerm target
  with decideModeEquality dataSet (mode oneTerm) target
... | yes equality =
  trans
    (integralCong dataSet
      (λ point →
        Algebra.complexMultiplyAssociative
          (coefficient oneTerm)
          (character dataSet (mode oneTerm) point)
          (conjugateCharacter dataSet target point)))
    (trans
      (integralScale dataSet
        (coefficient oneTerm)
        (λ point →
          C3.complexMultiply
            (character dataSet (mode oneTerm) point)
            (conjugateCharacter dataSet target point)))
      (trans
        (cong
          (C3.complexMultiply (coefficient oneTerm))
          (orthogonality dataSet (mode oneTerm) target))
        (complexMultiplyOneRight (coefficient oneTerm))))
... | no inequality =
  trans
    (integralCong dataSet
      (λ point →
        Algebra.complexMultiplyAssociative
          (coefficient oneTerm)
          (character dataSet (mode oneTerm) point)
          (conjugateCharacter dataSet target point)))
    (trans
      (integralScale dataSet
        (coefficient oneTerm)
        (λ point →
          C3.complexMultiply
            (character dataSet (mode oneTerm) point)
            (conjugateCharacter dataSet target point)))
      (trans
        (cong
          (C3.complexMultiply (coefficient oneTerm))
          (orthogonality dataSet (mode oneTerm) target))
        (Algebra.complexMultiplyZeroRight (coefficient oneTerm))))

polynomialCoefficientExtraction :
  ∀ {r} {F : C3.RealField r}
    (dataSet : TorusCharacterIntegral F)
    (terms : List (TorusTerm F (Mode dataSet)))
    (target : Mode dataSet) →
  coefficientIntegral dataSet terms target
  ≡ selectedCoefficient dataSet terms target
polynomialCoefficientExtraction dataSet [] target =
  trans
    (integralCong dataSet
      (λ point →
        Algebra.complexMultiplyZeroLeft
          (conjugateCharacter dataSet target point)))
    (integralZero dataSet)
polynomialCoefficientExtraction dataSet (oneTerm ∷ terms) target =
  trans
    (integralCong dataSet
      (λ point →
        Ring.complexDistributeRight
          (termValue dataSet oneTerm point)
          (polynomialValue dataSet terms point)
          (conjugateCharacter dataSet target point)))
    (trans
      (integralAdd dataSet
        (λ point →
          C3.complexMultiply
            (termValue dataSet oneTerm point)
            (conjugateCharacter dataSet target point))
        (λ point →
          C3.complexMultiply
            (polynomialValue dataSet terms point)
            (conjugateCharacter dataSet target point)))
      (cong₂ C3.complexAdd
        (singleTermCoefficientExtraction dataSet oneTerm target)
        (polynomialCoefficientExtraction dataSet terms target)))

torusCharacterMultiplication :
  ∀ {r} {F : C3.RealField r}
    (dataSet : TorusCharacterIntegral F)
    (left right : Mode dataSet)
    (point : Point dataSet) →
  C3.complexMultiply
    (character dataSet left point)
    (character dataSet right point)
  ≡ characterProduct dataSet left right point
torusCharacterMultiplication = characterMultiply

torusCharacterConjugation :
  ∀ {r} {F : C3.RealField r}
    (dataSet : TorusCharacterIntegral F)
    (modeValue : Mode dataSet)
    (point : Point dataSet) →
  C3.complexConjugate (character dataSet modeValue point)
  ≡ conjugateCharacter dataSet modeValue point
torusCharacterConjugation = characterConjugate

torusCharacterOrthogonality :
  ∀ {r} {F : C3.RealField r}
    (dataSet : TorusCharacterIntegral F)
    (left right : Mode dataSet) →
  integral dataSet
    (λ point →
      C3.complexMultiply
        (character dataSet left point)
        (conjugateCharacter dataSet right point))
  ≡ kroneckerComplex (decideModeEquality dataSet) left right
torusCharacterOrthogonality = orthogonality
