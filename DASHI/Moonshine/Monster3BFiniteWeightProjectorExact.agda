module DASHI.Moonshine.Monster3BFiniteWeightProjectorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- DASHI CONTRIBUTION
--
-- Add an actual finite diagonal weight projector to the 729 x 90 model.
-- Its coefficient is one exactly on the selected X=F3^6 weight and zero
-- elsewhere.  The coefficient is idempotent and covariant under all six
-- translation generators.  Pairwise orthogonality and the full 729-projector
-- resolution on the actual Monster zeta sector remain separate promotion
-- obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Fin.Base using (Fin)
open import Relation.Binary.PropositionalEquality using (cong)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteProjectorModelExact as Model

infixr 4 _and_

_and_ : Bool → Bool → Bool
false and right = false
true and right = right

tritEqual : Trit → Trit → Bool
tritEqual neg neg = true
tritEqual neg zer = false
tritEqual neg pos = false
tritEqual zer neg = false
tritEqual zer zer = true
tritEqual zer pos = false
tritEqual pos neg = false
tritEqual pos zer = false
tritEqual pos pos = true

tritEqualRefl : ∀ value → tritEqual value value ≡ true
tritEqualRefl neg = refl
tritEqualRefl zer = refl
tritEqualRefl pos = refl

tritEqualIncrement : ∀ left right →
  tritEqual (H.increment left) (H.increment right)
  ≡ tritEqual left right
tritEqualIncrement neg neg = refl
tritEqualIncrement neg zer = refl
tritEqualIncrement neg pos = refl
tritEqualIncrement zer neg = refl
tritEqualIncrement zer zer = refl
tritEqualIncrement zer pos = refl
tritEqualIncrement pos neg = refl
tritEqualIncrement pos zer = refl
tritEqualIncrement pos pos = refl

x6Equal : H.X6 → H.X6 → Bool
x6Equal (H.x6 a0 a1 a2 a3 a4 a5) (H.x6 b0 b1 b2 b3 b4 b5) =
  tritEqual a0 b0 and
  (tritEqual a1 b1 and
  (tritEqual a2 b2 and
  (tritEqual a3 b3 and
  (tritEqual a4 b4 and tritEqual a5 b5))))

x6EqualRefl : ∀ value → x6Equal value value ≡ true
x6EqualRefl (H.x6 a0 a1 a2 a3 a4 a5)
  rewrite tritEqualRefl a0
        | tritEqualRefl a1
        | tritEqualRefl a2
        | tritEqualRefl a3
        | tritEqualRefl a4
        | tritEqualRefl a5 = refl

x6EqualTranslationCovariant : ∀ axis left right →
  x6Equal (H.translate axis left) (H.translate axis right)
  ≡ x6Equal left right
x6EqualTranslationCovariant H.axis0
    (H.x6 a0 a1 a2 a3 a4 a5) (H.x6 b0 b1 b2 b3 b4 b5)
  rewrite tritEqualIncrement a0 b0 = refl
x6EqualTranslationCovariant H.axis1
    (H.x6 a0 a1 a2 a3 a4 a5) (H.x6 b0 b1 b2 b3 b4 b5)
  rewrite tritEqualIncrement a1 b1 = refl
x6EqualTranslationCovariant H.axis2
    (H.x6 a0 a1 a2 a3 a4 a5) (H.x6 b0 b1 b2 b3 b4 b5)
  rewrite tritEqualIncrement a2 b2 = refl
x6EqualTranslationCovariant H.axis3
    (H.x6 a0 a1 a2 a3 a4 a5) (H.x6 b0 b1 b2 b3 b4 b5)
  rewrite tritEqualIncrement a3 b3 = refl
x6EqualTranslationCovariant H.axis4
    (H.x6 a0 a1 a2 a3 a4 a5) (H.x6 b0 b1 b2 b3 b4 b5)
  rewrite tritEqualIncrement a4 b4 = refl
x6EqualTranslationCovariant H.axis5
    (H.x6 a0 a1 a2 a3 a4 a5) (H.x6 b0 b1 b2 b3 b4 b5)
  rewrite tritEqualIncrement a5 b5 = refl

boolCoefficient : Bool → Nat
boolCoefficient false = 0
boolCoefficient true = 1

weightProjectorCoefficient : H.X6 → Model.ZetaModelBasis → Nat
weightProjectorCoefficient selected basis =
  boolCoefficient (x6Equal selected (Model.weightPosition basis))

weightProjectorCoefficientIdempotent : ∀ selected basis →
  weightProjectorCoefficient selected basis
  * weightProjectorCoefficient selected basis
  ≡ weightProjectorCoefficient selected basis
weightProjectorCoefficientIdempotent selected basis
  with x6Equal selected (Model.weightPosition basis)
... | false = refl
... | true = refl

basisAt : H.X6 → Fin 90 → Model.ZetaModelBasis
basisAt position multiplicity = Model.zetaBasis position multiplicity

weightProjectorOwnWeight : ∀ position multiplicity →
  weightProjectorCoefficient position (basisAt position multiplicity) ≡ 1
weightProjectorOwnWeight position multiplicity
  rewrite x6EqualRefl position = refl

translatedProjectorCoefficient :
  H.Axis6 → H.X6 → Model.ZetaModelBasis → Nat
translatedProjectorCoefficient axis selected basis =
  weightProjectorCoefficient
    (H.translate axis selected)
    (Model.translatedBasis axis basis)

translatedProjectorCovariant : ∀ axis selected basis →
  translatedProjectorCoefficient axis selected basis
  ≡ weightProjectorCoefficient selected basis
translatedProjectorCovariant axis selected basis =
  cong boolCoefficient
    (x6EqualTranslationCovariant
      axis selected (Model.weightPosition basis))

record ProjectorResolutionBoundary : Set where
  constructor projectorResolutionBoundary
  field
    pointwiseProjectorIdempotenceProved : Bool
    pointwiseProjectorIdempotenceProvedIsTrue :
      pointwiseProjectorIdempotenceProved ≡ true

    translationCovarianceProved : Bool
    translationCovarianceProvedIsTrue :
      translationCovarianceProved ≡ true

    allTranslatedProjectorsOrthogonalOnActualSector : Bool
    allTranslatedProjectorsOrthogonalOnActualSectorIsFalse :
      allTranslatedProjectorsOrthogonalOnActualSector ≡ false

    allTranslatedProjectorsResolveActualSectorIdentity : Bool
    allTranslatedProjectorsResolveActualSectorIdentityIsFalse :
      allTranslatedProjectorsResolveActualSectorIdentity ≡ false

canonicalProjectorResolutionBoundary : ProjectorResolutionBoundary
canonicalProjectorResolutionBoundary =
  projectorResolutionBoundary true refl true refl false refl false refl
