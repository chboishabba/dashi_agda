module DASHI.Moonshine.Monster3BMultiplicityCharacterProjectorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- R. W. Barraclough and R. A. Wilson,
-- "The Character Table of a Maximal Subgroup of the Monster",
-- LMS Journal of Computation and Mathematics 10 (2007), 161--175.
-- DOI: 10.1112/S1461157000001352.
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- DASHI CONTRIBUTION
--
-- Isolate the finite projector-trace calculation needed to test the
-- 90-dimensional multiplicity character.  The actual class embedding and
-- character values remain explicit inputs; no guessed normalizer matrices are
-- introduced.  The exact isotypy signature 65610 = 90*729 and the proposed
-- 12+78 decomposition are independently regression-checked.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Moonshine.Monster3BHeisenbergMultiplicityExact as Multiplicity

append : ∀ {A : Set} → List A → List A → List A
append [] right = right
append (value ∷ values) right = value ∷ append values right

weightedTraceSum :
  ∀ {A : Set} → List A → (A → ℚ) → (A → ℚ) → ℚ
weightedTraceSum [] weight trace = 0ℚ
weightedTraceSum (value ∷ values) weight trace =
  weight value * trace value
  + weightedTraceSum values weight trace

weightedTraceAppend :
  ∀ {A : Set}
    (left right : List A)
    (weight trace : A → ℚ) →
  weightedTraceSum (append left right) weight trace
  ≡ weightedTraceSum left weight trace
    + weightedTraceSum right weight trace
weightedTraceAppend [] right weight trace =
  sym (ℚP.+-identityˡ (weightedTraceSum right weight trace))
weightedTraceAppend (value ∷ values) right weight trace
  rewrite weightedTraceAppend values right weight trace =
  sym
    (ℚP.+-assoc
      (weight value * trace value)
      (weightedTraceSum values weight trace)
      (weightedTraceSum right weight trace))

record ProjectorTraceInput : Set₁ where
  field
    AbelianClass : Set
    classEnumeration : List AbelianClass
    inverseCharacterWeight : AbelianClass → ℚ
    ambientCharacterAtProduct : AbelianClass → ℚ
    normalization : ℚ

open ProjectorTraceInput public

multiplicityProjectorTrace : ProjectorTraceInput → ℚ
multiplicityProjectorTrace input =
  normalization input
  * weightedTraceSum
      (classEnumeration input)
      (inverseCharacterWeight input)
      (ambientCharacterAtProduct input)

multiplicityTraceProjectorFormula :
  ∀ input →
  multiplicityProjectorTrace input
  ≡ normalization input
    * weightedTraceSum
        (classEnumeration input)
        (inverseCharacterWeight input)
        (ambientCharacterAtProduct input)
multiplicityTraceProjectorFormula input = refl

heisenbergDegree multiplicityDegree zetaSectorDegree : Nat
heisenbergDegree = Multiplicity.threePowerSix
multiplicityDegree = Multiplicity.multiplicityDegree
zetaSectorDegree = heisenbergDegree * multiplicityDegree

heisenbergDegreeIs729 : heisenbergDegree ≡ 729
heisenbergDegreeIs729 = refl

multiplicityDegreeIs90 : multiplicityDegree ≡ 90
multiplicityDegreeIs90 = refl

zetaSectorDegreeIs65610 : zetaSectorDegree ≡ 65610
zetaSectorDegreeIs65610 = refl

multiplicityTwelvePlusSeventyEight :
  Multiplicity.naturalSuzukiDegree
  + Multiplicity.symmetricSquareDualDegree
  ≡ multiplicityDegree
multiplicityTwelvePlusSeventyEight = refl

record MultiplicityCharacterCertificate : Set₁ where
  field
    certifiedAClassEmbedding : Set
    inertiaStabilizesChiZeta : Set
    multiplicityCharacterTable : Set
    multiplicityInnerProductsIntegral : Set
    multiplicityCharacterEqualsTwelvePlusSeventyEight : Set

record MultiplicityCharacterBoundary : Set where
  constructor multiplicityCharacterBoundary
  field
    projectorTraceFormulaFormalized : Bool
    projectorTraceFormulaFormalizedIsTrue :
      projectorTraceFormulaFormalized ≡ true

    isotypyDimensionSignatureChecked : Bool
    isotypyDimensionSignatureCheckedIsTrue :
      isotypyDimensionSignatureChecked ≡ true

    actualAClassEmbeddingCertified : Bool
    actualAClassEmbeddingCertifiedIsFalse :
      actualAClassEmbeddingCertified ≡ false

    actualMultiplicityCharacterCertified : Bool
    actualMultiplicityCharacterCertifiedIsFalse :
      actualMultiplicityCharacterCertified ≡ false

    twelvePlusSeventyEightProvedForActualMultiplicityModule : Bool
    twelvePlusSeventyEightProvedForActualMultiplicityModuleIsFalse :
      twelvePlusSeventyEightProvedForActualMultiplicityModule ≡ false

canonicalMultiplicityCharacterBoundary : MultiplicityCharacterBoundary
canonicalMultiplicityCharacterBoundary =
  multiplicityCharacterBoundary
    true refl true refl false refl false refl false refl
