module DASHI.Foundations.TernaryEndomorphismS3ActionLawsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- John D. Dixon and Brian Mortimer,
-- "Permutation Groups", Graduate Texts in Mathematics 163,
-- Springer, 1996.
-- DOI: 10.1007/978-1-4612-0731-3.
--
-- DASHI CONTRIBUTION
--
-- Close the conjugation operation from TernaryEndomorphismConjugacyExact into
-- a genuine action of the exact S3 group surface. The proof is extensional on
-- the repository's lossless three-output code, so no function extensionality
-- postulate is required.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

import Base369 as Base
import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Conj
import DASHI.Foundations.TernaryPermutationS3LawsExact as S3

------------------------------------------------------------------------
-- Equality of level-two codes from equality at all three ternary inputs.
------------------------------------------------------------------------

codeExtensional :
  (left right : Tower.LevelTwoCode) →
  ((input : Base.TriTruth) →
    Tower.decodeLevelTwo left input ≡ Tower.decodeLevelTwo right input) →
  left ≡ right
codeExtensional
  (leftLow , (leftMid , leftHigh))
  (rightLow , (rightMid , rightHigh))
  pointwise
  with pointwise Base.tri-low
     | pointwise Base.tri-mid
     | pointwise Base.tri-high
... | refl | refl | refl = refl

decodeConjugateAt :
  (permutation : Conj.TriPermutation) →
  (code : Tower.LevelTwoCode) →
  (input : Base.TriTruth) →
  Tower.decodeLevelTwo (Conj.conjugateCode permutation code) input
  ≡
  Conj.applyPermutation permutation
    (Tower.decodeLevelTwo code
      (Conj.applyPermutation
        (Conj.inversePermutation permutation) input))
decodeConjugateAt permutation code input =
  Tower.levelTwoDecodeEncodePointwise
    (λ x →
      Conj.applyPermutation permutation
        (Tower.decodeLevelTwo code
          (Conj.applyPermutation
            (Conj.inversePermutation permutation) x)))
    input

------------------------------------------------------------------------
-- Inversion reverses permutation multiplication.
------------------------------------------------------------------------

inverseProduct :
  (left right : Conj.TriPermutation) →
  Conj.inversePermutation (S3._∙_ left right)
  ≡
  S3._∙_
    (Conj.inversePermutation right)
    (Conj.inversePermutation left)
inverseProduct Conj.permIdentity Conj.permIdentity = refl
inverseProduct Conj.permIdentity Conj.permRotate = refl
inverseProduct Conj.permIdentity Conj.permRotate2 = refl
inverseProduct Conj.permIdentity Conj.permSwapLowMid = refl
inverseProduct Conj.permIdentity Conj.permSwapLowHigh = refl
inverseProduct Conj.permIdentity Conj.permSwapMidHigh = refl
inverseProduct Conj.permRotate Conj.permIdentity = refl
inverseProduct Conj.permRotate Conj.permRotate = refl
inverseProduct Conj.permRotate Conj.permRotate2 = refl
inverseProduct Conj.permRotate Conj.permSwapLowMid = refl
inverseProduct Conj.permRotate Conj.permSwapLowHigh = refl
inverseProduct Conj.permRotate Conj.permSwapMidHigh = refl
inverseProduct Conj.permRotate2 Conj.permIdentity = refl
inverseProduct Conj.permRotate2 Conj.permRotate = refl
inverseProduct Conj.permRotate2 Conj.permRotate2 = refl
inverseProduct Conj.permRotate2 Conj.permSwapLowMid = refl
inverseProduct Conj.permRotate2 Conj.permSwapLowHigh = refl
inverseProduct Conj.permRotate2 Conj.permSwapMidHigh = refl
inverseProduct Conj.permSwapLowMid Conj.permIdentity = refl
inverseProduct Conj.permSwapLowMid Conj.permRotate = refl
inverseProduct Conj.permSwapLowMid Conj.permRotate2 = refl
inverseProduct Conj.permSwapLowMid Conj.permSwapLowMid = refl
inverseProduct Conj.permSwapLowMid Conj.permSwapLowHigh = refl
inverseProduct Conj.permSwapLowMid Conj.permSwapMidHigh = refl
inverseProduct Conj.permSwapLowHigh Conj.permIdentity = refl
inverseProduct Conj.permSwapLowHigh Conj.permRotate = refl
inverseProduct Conj.permSwapLowHigh Conj.permRotate2 = refl
inverseProduct Conj.permSwapLowHigh Conj.permSwapLowMid = refl
inverseProduct Conj.permSwapLowHigh Conj.permSwapLowHigh = refl
inverseProduct Conj.permSwapLowHigh Conj.permSwapMidHigh = refl
inverseProduct Conj.permSwapMidHigh Conj.permIdentity = refl
inverseProduct Conj.permSwapMidHigh Conj.permRotate = refl
inverseProduct Conj.permSwapMidHigh Conj.permRotate2 = refl
inverseProduct Conj.permSwapMidHigh Conj.permSwapLowMid = refl
inverseProduct Conj.permSwapMidHigh Conj.permSwapLowHigh = refl
inverseProduct Conj.permSwapMidHigh Conj.permSwapMidHigh = refl

------------------------------------------------------------------------
-- Identity and composition laws for conjugation.
------------------------------------------------------------------------

conjugateIdentity :
  (code : Tower.LevelTwoCode) →
  Conj.conjugateCode Conj.permIdentity code ≡ code
conjugateIdentity code =
  codeExtensional
    (Conj.conjugateCode Conj.permIdentity code)
    code
    (λ input → decodeConjugateAt Conj.permIdentity code input)

conjugateCompositionAt :
  (left right : Conj.TriPermutation) →
  (code : Tower.LevelTwoCode) →
  (input : Base.TriTruth) →
  Tower.decodeLevelTwo
    (Conj.conjugateCode (S3._∙_ left right) code)
    input
  ≡
  Tower.decodeLevelTwo
    (Conj.conjugateCode left (Conj.conjugateCode right code))
    input
conjugateCompositionAt left right code input
  rewrite decodeConjugateAt (S3._∙_ left right) code input
        | inverseProduct left right
        | S3.applyComposition
            (Conj.inversePermutation right)
            (Conj.inversePermutation left)
            input
        | S3.applyComposition
            left right
            (Tower.decodeLevelTwo code
              (Conj.applyPermutation (Conj.inversePermutation right)
                (Conj.applyPermutation (Conj.inversePermutation left) input)))
        | decodeConjugateAt left (Conj.conjugateCode right code) input
        | decodeConjugateAt right code
            (Conj.applyPermutation (Conj.inversePermutation left) input) = refl

conjugateComposition :
  (left right : Conj.TriPermutation) →
  (code : Tower.LevelTwoCode) →
  Conj.conjugateCode (S3._∙_ left right) code
  ≡
  Conj.conjugateCode left (Conj.conjugateCode right code)
conjugateComposition left right code =
  codeExtensional
    (Conj.conjugateCode (S3._∙_ left right) code)
    (Conj.conjugateCode left (Conj.conjugateCode right code))
    (conjugateCompositionAt left right code)

record TernaryEndomorphismS3ActionSurface : Set where
  field
    act : Conj.TriPermutation → Tower.LevelTwoCode → Tower.LevelTwoCode
    identityActsTrivially :
      (code : Tower.LevelTwoCode) →
      act Conj.permIdentity code ≡ code
    multiplicationActsByComposition :
      (left right : Conj.TriPermutation) →
      (code : Tower.LevelTwoCode) →
      act (S3._∙_ left right) code
      ≡ act left (act right code)

canonicalTernaryEndomorphismS3ActionSurface :
  TernaryEndomorphismS3ActionSurface
canonicalTernaryEndomorphismS3ActionSurface =
  record
    { act = Conj.conjugateCode
    ; identityActsTrivially = conjugateIdentity
    ; multiplicationActsByComposition = conjugateComposition
    }
