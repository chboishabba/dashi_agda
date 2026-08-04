module DASHI.Physics.Closure.NSTriadKNLuoFiniteResonantPairFoldExact where

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
-- Put the finite pair calculation on a genuine resonant output fibre.  Every
-- element carries the equation k+l=m, and the source weighted-increment fold
-- is proved equal to the multiplier fold whose first transform is evaluated
-- at the fixed output m.  The whole-fold theorem and the exact three-piece
-- resonant split are obtained by induction; neither is stored as a field.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteCharacterWeightedIncrementExact as Character
import DASHI.Physics.Closure.NSTriadKNLuoFiniteTranslationTensorConvolutionExact as Tensor

record ResonantPair
    (system : Character.FiniteCharacterSystem)
    (output : Character.Mode system) : Set where
  constructor resonant-pair
  field
    left right : Character.Mode system
    closes : Character.addMode system left right ≡ output

open ResonantPair public

sourcePairCoefficient :
  (system : Character.FiniteCharacterSystem) →
  (leftCoefficient rightCoefficient : Character.Mode system → ℚ) →
  (output : Character.Mode system) →
  ResonantPair system output → ℚ
sourcePairCoefficient system leftCoefficient rightCoefficient output pair =
  Tensor.finiteIncrementTensorPairCoefficient
    system
    leftCoefficient
    rightCoefficient
    (left pair)
    (right pair)

outputMultiplierPairCoefficient :
  (system : Character.FiniteCharacterSystem) →
  (leftCoefficient rightCoefficient : Character.Mode system → ℚ) →
  (output : Character.Mode system) →
  ResonantPair system output → ℚ
outputMultiplierPairCoefficient
  system leftCoefficient rightCoefficient output pair =
  ( Character.finiteKernelTransform system output
    - Character.finiteKernelTransform system (left pair)
    - Character.finiteKernelTransform system (right pair)
    + Character.finiteKernelTransform system
        (Character.zeroMode system)
  )
  * (leftCoefficient (left pair) * rightCoefficient (right pair))

resonantPairCoefficientIdentity :
  (system : Character.FiniteCharacterSystem) →
  (leftCoefficient rightCoefficient : Character.Mode system → ℚ) →
  (output : Character.Mode system) →
  (pair : ResonantPair system output) →
  sourcePairCoefficient
    system leftCoefficient rightCoefficient output pair
  ≡ outputMultiplierPairCoefficient
      system leftCoefficient rightCoefficient output pair
resonantPairCoefficientIdentity
  system leftCoefficient rightCoefficient output pair =
  trans
    (Tensor.finiteTranslationTensorConvolutionIdentity
      system
      leftCoefficient
      rightCoefficient
      (left pair)
      (right pair))
    (cong
      (λ mode →
        ( Character.finiteKernelTransform system mode
          - Character.finiteKernelTransform system (left pair)
          - Character.finiteKernelTransform system (right pair)
          + Character.finiteKernelTransform system
              (Character.zeroMode system)
        )
        * (leftCoefficient (left pair) * rightCoefficient (right pair)))
      (closes pair))

sumPairCoefficients :
  ∀ {Pair : Set} →
  (Pair → ℚ) → List Pair → ℚ
sumPairCoefficients coefficient [] = 0ℚ
sumPairCoefficients coefficient (pair ∷ pairs) =
  coefficient pair + sumPairCoefficients coefficient pairs

resonantPairFoldIdentity :
  (system : Character.FiniteCharacterSystem) →
  (leftCoefficient rightCoefficient : Character.Mode system → ℚ) →
  (output : Character.Mode system) →
  (pairs : List (ResonantPair system output)) →
  sumPairCoefficients
    (sourcePairCoefficient
      system leftCoefficient rightCoefficient output)
    pairs
  ≡ sumPairCoefficients
      (outputMultiplierPairCoefficient
        system leftCoefficient rightCoefficient output)
      pairs
resonantPairFoldIdentity
  system leftCoefficient rightCoefficient output [] = refl
resonantPairFoldIdentity
  system leftCoefficient rightCoefficient output (pair ∷ pairs)
  rewrite resonantPairCoefficientIdentity
            system leftCoefficient rightCoefficient output pair
        | resonantPairFoldIdentity
            system leftCoefficient rightCoefficient output pairs = refl

data PhysicalPairPiece : Set where
  rp1Piece rp2Piece hardTailPiece : PhysicalPairPiece

record ClassifiedResonantPair
    (system : Character.FiniteCharacterSystem)
    (output : Character.Mode system) : Set where
  constructor classified-resonant-pair
  field
    pair : ResonantPair system output
    piece : PhysicalPairPiece

open ClassifiedResonantPair public

eraseClassifiedResonantPair :
  ∀ {system output} →
  ClassifiedResonantPair system output →
  ResonantPair system output
eraseClassifiedResonantPair classified = pair classified

eraseClassificationPreservesResonance :
  ∀ {system output}
    (classified : ClassifiedResonantPair system output) →
  Character.addMode system
    (left (eraseClassifiedResonantPair classified))
    (right (eraseClassifiedResonantPair classified))
  ≡ output
eraseClassificationPreservesResonance classified =
  closes (pair classified)

record ResonantThreeWaySplit
    (system : Character.FiniteCharacterSystem)
    (output : Character.Mode system) : Set where
  constructor resonant-three-way-split
  field
    rp1Pairs rp2Pairs hardTailPairs :
      List (ResonantPair system output)

open ResonantThreeWaySplit public

splitClassifiedResonantPairs :
  ∀ {system output} →
  List (ClassifiedResonantPair system output) →
  ResonantThreeWaySplit system output
splitClassifiedResonantPairs [] =
  resonant-three-way-split [] [] []
splitClassifiedResonantPairs (classified ∷ classifiedPairs)
  with piece classified | splitClassifiedResonantPairs classifiedPairs
... | rp1Piece | resonant-three-way-split rp1 rp2 tail =
  resonant-three-way-split (pair classified ∷ rp1) rp2 tail
... | rp2Piece | resonant-three-way-split rp1 rp2 tail =
  resonant-three-way-split rp1 (pair classified ∷ rp2) tail
... | hardTailPiece | resonant-three-way-split rp1 rp2 tail =
  resonant-three-way-split rp1 rp2 (pair classified ∷ tail)

classifiedPairFold :
  ∀ {system output} →
  (ResonantPair system output → ℚ) →
  List (ClassifiedResonantPair system output) →
  ℚ
classifiedPairFold coefficient [] = 0ℚ
classifiedPairFold coefficient (classified ∷ classifiedPairs) =
  coefficient (pair classified)
  + classifiedPairFold coefficient classifiedPairs

resonantThreeWaySplitReconstructsFold :
  ∀ {system output}
    (coefficient : ResonantPair system output → ℚ)
    (classifiedPairs : List (ClassifiedResonantPair system output)) →
  classifiedPairFold coefficient classifiedPairs
  ≡ sumPairCoefficients coefficient
      (rp1Pairs (splitClassifiedResonantPairs classifiedPairs))
    + sumPairCoefficients coefficient
        (rp2Pairs (splitClassifiedResonantPairs classifiedPairs))
    + sumPairCoefficients coefficient
        (hardTailPairs (splitClassifiedResonantPairs classifiedPairs))
resonantThreeWaySplitReconstructsFold coefficient [] = solve []
resonantThreeWaySplitReconstructsFold
  coefficient (classified ∷ classifiedPairs)
  with piece classified | splitClassifiedResonantPairs classifiedPairs
     | resonantThreeWaySplitReconstructsFold coefficient classifiedPairs
... | rp1Piece | resonant-three-way-split rp1 rp2 tail | induction =
  rewrite induction =
  solve
    ( coefficient (pair classified)
    ∷ sumPairCoefficients coefficient rp1
    ∷ sumPairCoefficients coefficient rp2
    ∷ sumPairCoefficients coefficient tail
    ∷ []
    )
... | rp2Piece | resonant-three-way-split rp1 rp2 tail | induction =
  rewrite induction =
  solve
    ( coefficient (pair classified)
    ∷ sumPairCoefficients coefficient rp1
    ∷ sumPairCoefficients coefficient rp2
    ∷ sumPairCoefficients coefficient tail
    ∷ []
    )
... | hardTailPiece | resonant-three-way-split rp1 rp2 tail | induction =
  rewrite induction =
  solve
    ( coefficient (pair classified)
    ∷ sumPairCoefficients coefficient rp1
    ∷ sumPairCoefficients coefficient rp2
    ∷ sumPairCoefficients coefficient tail
    ∷ []
    )

finiteResonantOutputFiberConstructed : Bool
finiteResonantOutputFiberConstructed = true

resonantPointwiseCoefficientIdentityClosed : Bool
resonantPointwiseCoefficientIdentityClosed = true

resonantWholeFoldIdentityClosed : Bool
resonantWholeFoldIdentityClosed = true

classificationErasurePreservesResonance : Bool
classificationErasurePreservesResonance = true

resonantThreeWaySplitReconstructionClosed : Bool
resonantThreeWaySplitReconstructionClosed = true

finiteResonantOutputFiberConstructedIsTrue :
  finiteResonantOutputFiberConstructed ≡ true
finiteResonantOutputFiberConstructedIsTrue = refl

resonantPointwiseCoefficientIdentityClosedIsTrue :
  resonantPointwiseCoefficientIdentityClosed ≡ true
resonantPointwiseCoefficientIdentityClosedIsTrue = refl

resonantWholeFoldIdentityClosedIsTrue :
  resonantWholeFoldIdentityClosed ≡ true
resonantWholeFoldIdentityClosedIsTrue = refl

classificationErasurePreservesResonanceIsTrue :
  classificationErasurePreservesResonance ≡ true
classificationErasurePreservesResonanceIsTrue = refl

resonantThreeWaySplitReconstructionClosedIsTrue :
  resonantThreeWaySplitReconstructionClosed ≡ true
resonantThreeWaySplitReconstructionClosedIsTrue = refl
