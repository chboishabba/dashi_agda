module DASHI.Physics.Closure.NSTriadKNLuoFiniteComplexResonantPairFoldExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Place the exact complex translation/increment coefficient on a genuine
-- resonant output fibre.  Every pair carries k+l=m.  The source coefficient
-- is proved equal to the complex multiplier coefficient evaluated at m, and
-- the identity is lifted to complete finite folds.  A total three-piece
-- classification then reconstructs the original fold as the rp1, rp2 and
-- hard-tail folds without duplication.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNLuoFiniteComplexWeightedIncrementExact as Complex
import DASHI.Physics.Closure.NSTriadKNLuoFiniteComplexTranslationTensorConvolutionExact as Tensor

record ComplexResonantPair
    {r : Level}
    {F : C3.RealField r}
    (system : Complex.FiniteComplexCharacterSystem F)
    (output : Complex.Mode system) : Set where
  constructor complex-resonant-pair
  field
    left right : Complex.Mode system
    closes : Complex.addMode system left right ≡ output

open ComplexResonantPair public

sourcePairCoefficient :
  ∀ {r} {F : C3.RealField r}
    (system : Complex.FiniteComplexCharacterSystem F)
    (leftCoefficient rightCoefficient : Complex.Mode system → C3.Complex F)
    (output : Complex.Mode system) →
  ComplexResonantPair system output → C3.Complex F
sourcePairCoefficient
  system leftCoefficient rightCoefficient output pair =
  Tensor.finiteComplexIncrementTensorPairCoefficient
    system
    leftCoefficient
    rightCoefficient
    (left pair)
    (right pair)

outputMultiplierPairCoefficient :
  ∀ {r} {F : C3.RealField r}
    (system : Complex.FiniteComplexCharacterSystem F)
    (leftCoefficient rightCoefficient : Complex.Mode system → C3.Complex F)
    (output : Complex.Mode system) →
  ComplexResonantPair system output → C3.Complex F
outputMultiplierPairCoefficient
  system leftCoefficient rightCoefficient output pair =
  C3.complexMultiply
    (C3.complexAdd
      (C3.complexSubtract
        (C3.complexSubtract
          (Complex.finiteComplexKernelTransform system output)
          (Complex.finiteComplexKernelTransform system (left pair)))
        (Complex.finiteComplexKernelTransform system (right pair)))
      (Complex.finiteComplexKernelTransform
        system (Complex.zeroMode system)))
    (C3.complexMultiply
      (leftCoefficient (left pair))
      (rightCoefficient (right pair)))

complexResonantPairCoefficientIdentity :
  ∀ {r} {F : C3.RealField r}
    (system : Complex.FiniteComplexCharacterSystem F)
    (leftCoefficient rightCoefficient : Complex.Mode system → C3.Complex F)
    (output : Complex.Mode system)
    (pair : ComplexResonantPair system output) →
  sourcePairCoefficient
    system leftCoefficient rightCoefficient output pair
  ≡ outputMultiplierPairCoefficient
      system leftCoefficient rightCoefficient output pair
complexResonantPairCoefficientIdentity
  system leftCoefficient rightCoefficient output pair =
  trans
    (Tensor.finiteComplexTranslationTensorConvolutionIdentity
      system
      leftCoefficient
      rightCoefficient
      (left pair)
      (right pair))
    (cong
      (λ mode →
        C3.complexMultiply
          (C3.complexAdd
            (C3.complexSubtract
              (C3.complexSubtract
                (Complex.finiteComplexKernelTransform system mode)
                (Complex.finiteComplexKernelTransform system (left pair)))
              (Complex.finiteComplexKernelTransform system (right pair)))
            (Complex.finiteComplexKernelTransform
              system (Complex.zeroMode system)))
          (C3.complexMultiply
            (leftCoefficient (left pair))
            (rightCoefficient (right pair))))
      (closes pair))

sumPairCoefficients :
  ∀ {r} {F : C3.RealField r} {Pair : Set} →
  (Pair → C3.Complex F) → List Pair → C3.Complex F
sumPairCoefficients {F = F} coefficient [] = C3.complexZero F
sumPairCoefficients coefficient (pair ∷ pairs) =
  C3.complexAdd
    (coefficient pair)
    (sumPairCoefficients coefficient pairs)

complexResonantPairFoldIdentity :
  ∀ {r} {F : C3.RealField r}
    (system : Complex.FiniteComplexCharacterSystem F)
    (leftCoefficient rightCoefficient : Complex.Mode system → C3.Complex F)
    (output : Complex.Mode system)
    (pairs : List (ComplexResonantPair system output)) →
  sumPairCoefficients
    (sourcePairCoefficient
      system leftCoefficient rightCoefficient output)
    pairs
  ≡ sumPairCoefficients
      (outputMultiplierPairCoefficient
        system leftCoefficient rightCoefficient output)
      pairs
complexResonantPairFoldIdentity
  system leftCoefficient rightCoefficient output [] = refl
complexResonantPairFoldIdentity
  system leftCoefficient rightCoefficient output (pair ∷ pairs)
  rewrite complexResonantPairCoefficientIdentity
            system leftCoefficient rightCoefficient output pair
        | complexResonantPairFoldIdentity
            system leftCoefficient rightCoefficient output pairs = refl

data ComplexPhysicalPairPiece : Set where
  rp1Piece rp2Piece hardTailPiece : ComplexPhysicalPairPiece

record ClassifiedComplexResonantPair
    {r : Level}
    {F : C3.RealField r}
    (system : Complex.FiniteComplexCharacterSystem F)
    (output : Complex.Mode system) : Set where
  constructor classified-complex-resonant-pair
  field
    pair : ComplexResonantPair system output
    piece : ComplexPhysicalPairPiece

open ClassifiedComplexResonantPair public

record ComplexResonantThreeWaySplit
    {r : Level}
    {F : C3.RealField r}
    (system : Complex.FiniteComplexCharacterSystem F)
    (output : Complex.Mode system) : Set where
  constructor complex-resonant-three-way-split
  field
    rp1Pairs rp2Pairs hardTailPairs :
      List (ComplexResonantPair system output)

open ComplexResonantThreeWaySplit public

splitClassifiedPairs :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    {output : Complex.Mode system} →
  List (ClassifiedComplexResonantPair system output) →
  ComplexResonantThreeWaySplit system output
splitClassifiedPairs [] =
  complex-resonant-three-way-split [] [] []
splitClassifiedPairs (classified ∷ classifiedPairs)
  with piece classified | splitClassifiedPairs classifiedPairs
... | rp1Piece | complex-resonant-three-way-split rp1 rp2 tail =
  complex-resonant-three-way-split (pair classified ∷ rp1) rp2 tail
... | rp2Piece | complex-resonant-three-way-split rp1 rp2 tail =
  complex-resonant-three-way-split rp1 (pair classified ∷ rp2) tail
... | hardTailPiece | complex-resonant-three-way-split rp1 rp2 tail =
  complex-resonant-three-way-split rp1 rp2 (pair classified ∷ tail)

classifiedPairFold :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    {output : Complex.Mode system} →
  (ComplexResonantPair system output → C3.Complex F) →
  List (ClassifiedComplexResonantPair system output) →
  C3.Complex F
classifiedPairFold {F = F} coefficient [] = C3.complexZero F
classifiedPairFold coefficient (classified ∷ classifiedPairs) =
  C3.complexAdd
    (coefficient (pair classified))
    (classifiedPairFold coefficient classifiedPairs)

complexThreeWaySplitReconstructsFold :
  ∀ {r} {F : C3.RealField r}
    {system : Complex.FiniteComplexCharacterSystem F}
    {output : Complex.Mode system}
    (coefficient : ComplexResonantPair system output → C3.Complex F)
    (classifiedPairs : List (ClassifiedComplexResonantPair system output)) →
  classifiedPairFold coefficient classifiedPairs
  ≡ C3.complexAdd
      (C3.complexAdd
        (sumPairCoefficients coefficient
          (rp1Pairs (splitClassifiedPairs classifiedPairs)))
        (sumPairCoefficients coefficient
          (rp2Pairs (splitClassifiedPairs classifiedPairs))))
      (sumPairCoefficients coefficient
        (hardTailPairs (splitClassifiedPairs classifiedPairs)))
complexThreeWaySplitReconstructsFold {F = F} coefficient [] =
  R.solve 0
    (λ →
      R.Κ (C3.complexZero F)
      R.⊜
      ((R.Κ (C3.complexZero F) R.⊕ R.Κ (C3.complexZero F))
        R.⊕ R.Κ (C3.complexZero F)))
    refl
  where module R = Ring.Solver F
complexThreeWaySplitReconstructsFold
  {F = F} coefficient (classified ∷ classifiedPairs)
  with piece classified | splitClassifiedPairs classifiedPairs
     | complexThreeWaySplitReconstructsFold coefficient classifiedPairs
... | rp1Piece | complex-resonant-three-way-split rp1 rp2 tail | induction =
  rewrite induction =
  R.solve 4
    (λ head rp1Value rp2Value tailValue →
      (head R.⊕ ((rp1Value R.⊕ rp2Value) R.⊕ tailValue))
      R.⊜ (((head R.⊕ rp1Value) R.⊕ rp2Value) R.⊕ tailValue))
    refl
    (coefficient (pair classified))
    (sumPairCoefficients coefficient rp1)
    (sumPairCoefficients coefficient rp2)
    (sumPairCoefficients coefficient tail)
  where module R = Ring.Solver F
... | rp2Piece | complex-resonant-three-way-split rp1 rp2 tail | induction =
  rewrite induction =
  R.solve 4
    (λ head rp1Value rp2Value tailValue →
      (head R.⊕ ((rp1Value R.⊕ rp2Value) R.⊕ tailValue))
      R.⊜ ((rp1Value R.⊕ (head R.⊕ rp2Value)) R.⊕ tailValue))
    refl
    (coefficient (pair classified))
    (sumPairCoefficients coefficient rp1)
    (sumPairCoefficients coefficient rp2)
    (sumPairCoefficients coefficient tail)
  where module R = Ring.Solver F
... | hardTailPiece | complex-resonant-three-way-split rp1 rp2 tail | induction =
  rewrite induction =
  R.solve 4
    (λ head rp1Value rp2Value tailValue →
      (head R.⊕ ((rp1Value R.⊕ rp2Value) R.⊕ tailValue))
      R.⊜ ((rp1Value R.⊕ rp2Value) R.⊕ (head R.⊕ tailValue)))
    refl
    (coefficient (pair classified))
    (sumPairCoefficients coefficient rp1)
    (sumPairCoefficients coefficient rp2)
    (sumPairCoefficients coefficient tail)
  where module R = Ring.Solver F

finiteComplexResonantPairIdentityClosed : Bool
finiteComplexResonantPairIdentityClosed = true

finiteComplexResonantFoldIdentityClosed : Bool
finiteComplexResonantFoldIdentityClosed = true

finiteComplexThreeWaySplitClosed : Bool
finiteComplexThreeWaySplitClosed = true

finiteComplexResonantPairIdentityClosedIsTrue :
  finiteComplexResonantPairIdentityClosed ≡ true
finiteComplexResonantPairIdentityClosedIsTrue = refl

finiteComplexResonantFoldIdentityClosedIsTrue :
  finiteComplexResonantFoldIdentityClosed ≡ true
finiteComplexResonantFoldIdentityClosedIsTrue = refl

finiteComplexThreeWaySplitClosedIsTrue :
  finiteComplexThreeWaySplitClosed ≡ true
finiteComplexThreeWaySplitClosedIsTrue = refl
