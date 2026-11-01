module DASHI.Moonshine.Monster3BFiniteProjectorModelExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- R. W. Barraclough and R. A. Wilson,
-- "The Character Table of a Maximal Subgroup of the Monster",
-- LMS Journal of Computation and Mathematics 10 (2007), 161--175.
-- DOI: 10.1112/S1461157000001352.
--
-- DASHI CONTRIBUTION
--
-- Build the finite index model behind the proposed chi_zeta projector route.
-- The model basis is X x Fin 90, where X=F3^6 has 729 states.  Translation
-- acts only on the X coordinate, and the evaluation map from a translated
-- weight-space label to the model basis is literally invertible and
-- translation-equivariant.  This realizes the 729 x 90 = 65610 mechanism
-- without any 65610-by-65610 matrices.
--
-- This file deliberately does not identify the model with the actual Monster
-- zeta eigenspace.  That remaining intertwiner is kept as a false boundary.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Fin.Base using (Fin)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteHeisenbergPermutationExact as Perm
import DASHI.Moonshine.Monster3BHeisenbergMultiplicityExact as Multiplicity

record ZetaModelBasis : Set where
  constructor zetaBasis
  field
    weightPosition : H.X6
    multiplicityCoordinate : Fin 90

open ZetaModelBasis public

translatedBasis : H.Axis6 → ZetaModelBasis → ZetaModelBasis
translatedBasis axis basis =
  zetaBasis
    (H.translate axis (weightPosition basis))
    (multiplicityCoordinate basis)

inverseTranslatedBasis : H.Axis6 → ZetaModelBasis → ZetaModelBasis
inverseTranslatedBasis axis basis =
  zetaBasis
    (H.translateInverse axis (weightPosition basis))
    (multiplicityCoordinate basis)

inverseAfterTranslation :
  ∀ axis basis →
  inverseTranslatedBasis axis (translatedBasis axis basis) ≡ basis
inverseAfterTranslation axis (zetaBasis position multiplicity)
  rewrite Perm.translateInverseAfterTranslate axis position = refl

translationAfterInverse :
  ∀ axis basis →
  translatedBasis axis (inverseTranslatedBasis axis basis) ≡ basis
translationAfterInverse axis (zetaBasis position multiplicity)
  rewrite Perm.translateAfterTranslateInverse axis position = refl

record TranslatedMultiplicityLabel : Set where
  constructor translatedLabel
  field
    translationPosition : H.X6
    multiplicityLabel : Fin 90

open TranslatedMultiplicityLabel public

evaluationMap : TranslatedMultiplicityLabel → ZetaModelBasis
evaluationMap label =
  zetaBasis
    (translationPosition label)
    (multiplicityLabel label)

evaluationInverse : ZetaModelBasis → TranslatedMultiplicityLabel
evaluationInverse basis =
  translatedLabel
    (weightPosition basis)
    (multiplicityCoordinate basis)

evaluationLeftInverse :
  ∀ label → evaluationInverse (evaluationMap label) ≡ label
evaluationLeftInverse (translatedLabel position multiplicity) = refl

evaluationRightInverse :
  ∀ basis → evaluationMap (evaluationInverse basis) ≡ basis
evaluationRightInverse (zetaBasis position multiplicity) = refl

translateLabel :
  H.Axis6 → TranslatedMultiplicityLabel → TranslatedMultiplicityLabel
translateLabel axis label =
  translatedLabel
    (H.translate axis (translationPosition label))
    (multiplicityLabel label)

evaluationTranslationEquivariant :
  ∀ axis label →
  evaluationMap (translateLabel axis label)
  ≡ translatedBasis axis (evaluationMap label)
evaluationTranslationEquivariant axis
  (translatedLabel position multiplicity) = refl

weightSpaceCount multiplicitySpaceDimension zetaModelDimension : Nat
weightSpaceCount = H.schrodingerBasisDimension
multiplicitySpaceDimension = Multiplicity.multiplicityDegree
zetaModelDimension = weightSpaceCount * multiplicitySpaceDimension

weightSpaceCountIs729 : weightSpaceCount ≡ 729
weightSpaceCountIs729 = refl

multiplicitySpaceDimensionIs90 : multiplicitySpaceDimension ≡ 90
multiplicitySpaceDimensionIs90 = refl

zetaModelDimensionIs65610 : zetaModelDimension ≡ 65610
zetaModelDimensionIs65610 = refl

record ActualZetaIdentificationBoundary : Set where
  constructor actualZetaIdentificationBoundary
  field
    finite729By90ModelConstructed : Bool
    finite729By90ModelConstructedIsTrue :
      finite729By90ModelConstructed ≡ true

    evaluationMapConstructivelyInvertible : Bool
    evaluationMapConstructivelyInvertibleIsTrue :
      evaluationMapConstructivelyInvertible ≡ true

    evaluationMapTranslationEquivariant : Bool
    evaluationMapTranslationEquivariantIsTrue :
      evaluationMapTranslationEquivariant ≡ true

    actualMonsterZetaSectorIdentifiedWithModel : Bool
    actualMonsterZetaSectorIdentifiedWithModelIsFalse :
      actualMonsterZetaSectorIdentifiedWithModel ≡ false

    actualChiZetaProjectorResolutionCertified : Bool
    actualChiZetaProjectorResolutionCertifiedIsFalse :
      actualChiZetaProjectorResolutionCertified ≡ false

canonicalActualZetaIdentificationBoundary : ActualZetaIdentificationBoundary
canonicalActualZetaIdentificationBoundary =
  actualZetaIdentificationBoundary
    true refl true refl true refl false refl false refl
