module DASHI.Physics.Closure.NSTriadKNLuoTorusTrigonometricParsevalExact where

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
-- Derive finite Parseval directly on the torus-character carrier introduced
-- in NSTriadKNLuoTorusTrigonometricPolynomialExact.  The proof expands both
-- finite sums, applies normalized Haar-character orthogonality to every pair,
-- and folds the resulting Kronecker diagonal.  No cyclic primitive-root model
-- or sampled-DFT aliasing argument is used.
--
-- For a list with repeated modes the right side is the exact double
-- Kronecker sum, hence automatically computes the squared magnitude of the
-- aggregated coefficient.  A duplicate-free support list is the usual
-- single-sum Parseval statement.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNLuoTorusTrigonometricPolynomialExact as Torus

complexConjugateAdd :
  ∀ {r} {F : C3.RealField r}
    (left right : C3.Complex F) →
  C3.complexConjugate (C3.complexAdd left right)
  ≡ C3.complexAdd
      (C3.complexConjugate left)
      (C3.complexConjugate right)
complexConjugateAdd {F = F}
  (C3.complex leftReal leftImaginary)
  (C3.complex rightReal rightImaginary) =
  Algebra.complexExt refl
    (P.R.solve 2
      (λ leftValue rightValue →
        P.R.⊝ (leftValue P.R.⊕ rightValue)
        P.R.⊜
        (P.R.⊝ leftValue) P.R.⊕ (P.R.⊝ rightValue))
      refl leftImaginary rightImaginary)
  where
    module P = Algebra.Polynomial F

complexRegroupFour :
  ∀ {r} {F : C3.RealField r}
    (first second third fourth : C3.Complex F) →
  C3.complexMultiply
    (C3.complexMultiply first second)
    (C3.complexMultiply third fourth)
  ≡
  C3.complexMultiply
    (C3.complexMultiply first third)
    (C3.complexMultiply second fourth)
complexRegroupFour first second third fourth =
  trans
    (sym
      (Algebra.complexMultiplyAssociative
        (C3.complexMultiply first second)
        third
        fourth))
    (trans
      (cong
        (λ prefix → C3.complexMultiply prefix fourth)
        (trans
          (Algebra.complexMultiplyAssociative first second third)
          (trans
            (cong
              (C3.complexMultiply first)
              (Algebra.complexMultiplyCommutative second third))
            (sym
              (Algebra.complexMultiplyAssociative
                first third second)))))
      (Algebra.complexMultiplyAssociative
        (C3.complexMultiply first third)
        second
        fourth))

conjugateTermValue :
  ∀ {r} {F : C3.RealField r}
    (dataSet : Torus.TorusCharacterIntegral F) →
  Torus.TorusTerm F (Torus.Mode dataSet) →
  Torus.Point dataSet →
  C3.Complex F
conjugateTermValue dataSet oneTerm point =
  C3.complexMultiply
    (C3.complexConjugate (Torus.coefficient oneTerm))
    (Torus.conjugateCharacter dataSet (Torus.mode oneTerm) point)

conjugatePolynomialValue :
  ∀ {r} {F : C3.RealField r}
    (dataSet : Torus.TorusCharacterIntegral F) →
  List (Torus.TorusTerm F (Torus.Mode dataSet)) →
  Torus.Point dataSet →
  C3.Complex F
conjugatePolynomialValue dataSet [] point = C3.complexZero _
conjugatePolynomialValue dataSet (oneTerm ∷ terms) point =
  C3.complexAdd
    (conjugateTermValue dataSet oneTerm point)
    (conjugatePolynomialValue dataSet terms point)

conjugateTermMeaning :
  ∀ {r} {F : C3.RealField r}
    (dataSet : Torus.TorusCharacterIntegral F)
    (oneTerm : Torus.TorusTerm F (Torus.Mode dataSet))
    (point : Torus.Point dataSet) →
  C3.complexConjugate (Torus.termValue dataSet oneTerm point)
  ≡ conjugateTermValue dataSet oneTerm point
conjugateTermMeaning dataSet oneTerm point =
  trans
    (Algebra.complexConjugateMultiply
      (Torus.coefficient oneTerm)
      (Torus.character dataSet (Torus.mode oneTerm) point))
    (cong
      (C3.complexMultiply
        (C3.complexConjugate (Torus.coefficient oneTerm)))
      (Torus.characterConjugate
        dataSet (Torus.mode oneTerm) point))

conjugatePolynomialMeaning :
  ∀ {r} {F : C3.RealField r}
    (dataSet : Torus.TorusCharacterIntegral F)
    (terms : List (Torus.TorusTerm F (Torus.Mode dataSet)))
    (point : Torus.Point dataSet) →
  C3.complexConjugate (Torus.polynomialValue dataSet terms point)
  ≡ conjugatePolynomialValue dataSet terms point
conjugatePolynomialMeaning dataSet [] point =
  Algebra.complexConjugateZero
conjugatePolynomialMeaning dataSet (oneTerm ∷ terms) point =
  trans
    (complexConjugateAdd
      (Torus.termValue dataSet oneTerm point)
      (Torus.polynomialValue dataSet terms point))
    (cong₂ C3.complexAdd
      (conjugateTermMeaning dataSet oneTerm point)
      (conjugatePolynomialMeaning dataSet terms point))

pairCoefficientEnergy :
  ∀ {r} {F : C3.RealField r}
    (dataSet : Torus.TorusCharacterIntegral F) →
  Torus.TorusTerm F (Torus.Mode dataSet) →
  Torus.TorusTerm F (Torus.Mode dataSet) →
  C3.Complex F
pairCoefficientEnergy dataSet leftTerm rightTerm =
  C3.complexMultiply
    (C3.complexMultiply
      (Torus.coefficient leftTerm)
      (C3.complexConjugate (Torus.coefficient rightTerm)))
    (Torus.kroneckerComplex
      (Torus.decideModeEquality dataSet)
      (Torus.mode leftTerm)
      (Torus.mode rightTerm))

termAgainstCoefficientEnergy :
  ∀ {r} {F : C3.RealField r}
    (dataSet : Torus.TorusCharacterIntegral F) →
  Torus.TorusTerm F (Torus.Mode dataSet) →
  List (Torus.TorusTerm F (Torus.Mode dataSet)) →
  C3.Complex F
termAgainstCoefficientEnergy dataSet leftTerm [] = C3.complexZero _
termAgainstCoefficientEnergy dataSet leftTerm (rightTerm ∷ rightTerms) =
  C3.complexAdd
    (pairCoefficientEnergy dataSet leftTerm rightTerm)
    (termAgainstCoefficientEnergy dataSet leftTerm rightTerms)

polynomialCoefficientEnergy :
  ∀ {r} {F : C3.RealField r}
    (dataSet : Torus.TorusCharacterIntegral F) →
  List (Torus.TorusTerm F (Torus.Mode dataSet)) →
  List (Torus.TorusTerm F (Torus.Mode dataSet)) →
  C3.Complex F
polynomialCoefficientEnergy dataSet [] rightTerms = C3.complexZero _
polynomialCoefficientEnergy dataSet (leftTerm ∷ leftTerms) rightTerms =
  C3.complexAdd
    (termAgainstCoefficientEnergy dataSet leftTerm rightTerms)
    (polynomialCoefficientEnergy dataSet leftTerms rightTerms)

singlePairParseval :
  ∀ {r} {F : C3.RealField r}
    (dataSet : Torus.TorusCharacterIntegral F)
    (leftTerm rightTerm : Torus.TorusTerm F (Torus.Mode dataSet)) →
  Torus.integral dataSet
    (λ point →
      C3.complexMultiply
        (Torus.termValue dataSet leftTerm point)
        (conjugateTermValue dataSet rightTerm point))
  ≡ pairCoefficientEnergy dataSet leftTerm rightTerm
singlePairParseval dataSet leftTerm rightTerm =
  trans
    (Torus.integralCong dataSet
      (λ point →
        complexRegroupFour
          (Torus.coefficient leftTerm)
          (Torus.character dataSet (Torus.mode leftTerm) point)
          (C3.complexConjugate (Torus.coefficient rightTerm))
          (Torus.conjugateCharacter
            dataSet (Torus.mode rightTerm) point)))
    (trans
      (Torus.integralScale dataSet
        (C3.complexMultiply
          (Torus.coefficient leftTerm)
          (C3.complexConjugate (Torus.coefficient rightTerm)))
        (λ point →
          C3.complexMultiply
            (Torus.character dataSet (Torus.mode leftTerm) point)
            (Torus.conjugateCharacter
              dataSet (Torus.mode rightTerm) point)))
      (cong
        (C3.complexMultiply
          (C3.complexMultiply
            (Torus.coefficient leftTerm)
            (C3.complexConjugate (Torus.coefficient rightTerm))))
        (Torus.orthogonality
          dataSet (Torus.mode leftTerm) (Torus.mode rightTerm))))

singleTermAgainstPolynomialParseval :
  ∀ {r} {F : C3.RealField r}
    (dataSet : Torus.TorusCharacterIntegral F)
    (leftTerm : Torus.TorusTerm F (Torus.Mode dataSet))
    (rightTerms : List (Torus.TorusTerm F (Torus.Mode dataSet))) →
  Torus.integral dataSet
    (λ point →
      C3.complexMultiply
        (Torus.termValue dataSet leftTerm point)
        (conjugatePolynomialValue dataSet rightTerms point))
  ≡ termAgainstCoefficientEnergy dataSet leftTerm rightTerms
singleTermAgainstPolynomialParseval dataSet leftTerm [] =
  trans
    (Torus.integralCong dataSet
      (λ point →
        Algebra.complexMultiplyZeroRight
          (Torus.termValue dataSet leftTerm point)))
    (Torus.integralZero dataSet)
singleTermAgainstPolynomialParseval
  dataSet leftTerm (rightTerm ∷ rightTerms) =
  trans
    (Torus.integralCong dataSet
      (λ point →
        Ring.complexDistributeLeft
          (Torus.termValue dataSet leftTerm point)
          (conjugateTermValue dataSet rightTerm point)
          (conjugatePolynomialValue dataSet rightTerms point)))
    (trans
      (Torus.integralAdd dataSet
        (λ point →
          C3.complexMultiply
            (Torus.termValue dataSet leftTerm point)
            (conjugateTermValue dataSet rightTerm point))
        (λ point →
          C3.complexMultiply
            (Torus.termValue dataSet leftTerm point)
            (conjugatePolynomialValue dataSet rightTerms point)))
      (cong₂ C3.complexAdd
        (singlePairParseval dataSet leftTerm rightTerm)
        (singleTermAgainstPolynomialParseval
          dataSet leftTerm rightTerms)))

polynomialPairParseval :
  ∀ {r} {F : C3.RealField r}
    (dataSet : Torus.TorusCharacterIntegral F)
    (leftTerms rightTerms :
      List (Torus.TorusTerm F (Torus.Mode dataSet))) →
  Torus.integral dataSet
    (λ point →
      C3.complexMultiply
        (Torus.polynomialValue dataSet leftTerms point)
        (conjugatePolynomialValue dataSet rightTerms point))
  ≡ polynomialCoefficientEnergy dataSet leftTerms rightTerms
polynomialPairParseval dataSet [] rightTerms =
  trans
    (Torus.integralCong dataSet
      (λ point →
        Algebra.complexMultiplyZeroLeft
          (conjugatePolynomialValue dataSet rightTerms point)))
    (Torus.integralZero dataSet)
polynomialPairParseval dataSet (leftTerm ∷ leftTerms) rightTerms =
  trans
    (Torus.integralCong dataSet
      (λ point →
        Ring.complexDistributeRight
          (Torus.termValue dataSet leftTerm point)
          (Torus.polynomialValue dataSet leftTerms point)
          (conjugatePolynomialValue dataSet rightTerms point)))
    (trans
      (Torus.integralAdd dataSet
        (λ point →
          C3.complexMultiply
            (Torus.termValue dataSet leftTerm point)
            (conjugatePolynomialValue dataSet rightTerms point))
        (λ point →
          C3.complexMultiply
            (Torus.polynomialValue dataSet leftTerms point)
            (conjugatePolynomialValue dataSet rightTerms point)))
      (cong₂ C3.complexAdd
        (singleTermAgainstPolynomialParseval
          dataSet leftTerm rightTerms)
        (polynomialPairParseval dataSet leftTerms rightTerms)))

physicalPolynomialEnergy :
  ∀ {r} {F : C3.RealField r}
    (dataSet : Torus.TorusCharacterIntegral F) →
  List (Torus.TorusTerm F (Torus.Mode dataSet)) →
  C3.Complex F
physicalPolynomialEnergy dataSet terms =
  Torus.integral dataSet
    (λ point →
      C3.complexMultiply
        (Torus.polynomialValue dataSet terms point)
        (C3.complexConjugate
          (Torus.polynomialValue dataSet terms point)))

torusFiniteParseval :
  ∀ {r} {F : C3.RealField r}
    (dataSet : Torus.TorusCharacterIntegral F)
    (terms : List (Torus.TorusTerm F (Torus.Mode dataSet))) →
  physicalPolynomialEnergy dataSet terms
  ≡ polynomialCoefficientEnergy dataSet terms terms
torusFiniteParseval dataSet terms =
  trans
    (Torus.integralCong dataSet
      (λ point →
        cong
          (C3.complexMultiply
            (Torus.polynomialValue dataSet terms point))
          (conjugatePolynomialMeaning dataSet terms point)))
    (polynomialPairParseval dataSet terms terms)

singleModeParseval :
  ∀ {r} {F : C3.RealField r}
    (dataSet : Torus.TorusCharacterIntegral F)
    (oneTerm : Torus.TorusTerm F (Torus.Mode dataSet)) →
  physicalPolynomialEnergy dataSet (oneTerm ∷ [])
  ≡ C3.complexMultiply
      (Torus.coefficient oneTerm)
      (C3.complexConjugate (Torus.coefficient oneTerm))
singleModeParseval dataSet oneTerm
  with Torus.decideModeEquality dataSet
    (Torus.mode oneTerm) (Torus.mode oneTerm)
... | yes equality =
  trans
    (torusFiniteParseval dataSet (oneTerm ∷ []))
    (trans
      (cong
        (λ diagonal →
          C3.complexAdd
            (C3.complexAdd diagonal (C3.complexZero _))
            (C3.complexZero _))
        (Ring.complexMultiplyOneRight
          (C3.complexMultiply
            (Torus.coefficient oneTerm)
            (C3.complexConjugate (Torus.coefficient oneTerm)))))
      (trans
        (cong
          (λ inner → C3.complexAdd inner (C3.complexZero _))
          (Algebra.complexAddZeroRight
            (C3.complexMultiply
              (Torus.coefficient oneTerm)
              (C3.complexConjugate (Torus.coefficient oneTerm)))))
        (Algebra.complexAddZeroRight
          (C3.complexMultiply
            (Torus.coefficient oneTerm)
            (C3.complexConjugate (Torus.coefficient oneTerm))))))
... | no inequality = ⊥-elim (inequality refl)
