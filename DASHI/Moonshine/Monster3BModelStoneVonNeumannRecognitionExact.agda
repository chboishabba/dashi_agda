module DASHI.Moonshine.Monster3BModelStoneVonNeumannRecognitionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- I. M. Isaacs,
-- "Character Theory of Finite Groups",
-- Dover Publications, 1994 reprint of the 1976 edition.
-- ISBN: 978-0-486-68014-9; no DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Give the constructive finite-model content of the Stone--von Neumann step.
-- The evaluation map from translated weight labels to X x Fin 90 is an
-- explicit isomorphism, is equivariant under every standard translation, and
-- every nontrivial standard translation is fixed-point-free.  The last fact is
-- the concrete permutation-basis reason for zero trace on these noncentral
-- Weyl generators.
--
-- This is a theorem about the finite model.  Identifying the certified MN3B
-- restriction with this model remains a separate representation-theoretic
-- intertwiner obligation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteProjectorModelExact as Model

------------------------------------------------------------------------
-- Explicit isomorphism rather than an opaque Hom-space dimension receipt.
------------------------------------------------------------------------

record FiniteEvaluationIsomorphism : Set where
  constructor finite-evaluation-isomorphism
  field
    forward : Model.TranslatedMultiplicityLabel → Model.ZetaModelBasis
    inverse : Model.ZetaModelBasis → Model.TranslatedMultiplicityLabel
    inverseAfterForward :
      (label : Model.TranslatedMultiplicityLabel) →
      inverse (forward label) ≡ label
    forwardAfterInverse :
      (basis : Model.ZetaModelBasis) →
      forward (inverse basis) ≡ basis

open FiniteEvaluationIsomorphism public

canonicalFiniteEvaluationIsomorphism : FiniteEvaluationIsomorphism
canonicalFiniteEvaluationIsomorphism =
  finite-evaluation-isomorphism
    Model.evaluationMap
    Model.evaluationInverse
    Model.evaluationLeftInverse
    Model.evaluationRightInverse

evaluationMapIsIsomorphism :
  (label : Model.TranslatedMultiplicityLabel) →
  inverse canonicalFiniteEvaluationIsomorphism
    (forward canonicalFiniteEvaluationIsomorphism label)
  ≡ label
evaluationMapIsIsomorphism =
  inverseAfterForward canonicalFiniteEvaluationIsomorphism

evaluationMapIsETranslationEquivariant :
  (axis : H.Axis6) →
  (label : Model.TranslatedMultiplicityLabel) →
  Model.evaluationMap (Model.translateLabel axis label)
  ≡ Model.translatedBasis axis (Model.evaluationMap label)
evaluationMapIsETranslationEquivariant =
  Model.evaluationTranslationEquivariant

------------------------------------------------------------------------
-- Standard translations have no fixed coordinate in F_3^6.
------------------------------------------------------------------------

incrementHasNoFixedPoint :
  (value : Trit) → H.increment value ≡ value → ⊥
incrementHasNoFixedPoint neg ()
incrementHasNoFixedPoint zer ()
incrementHasNoFixedPoint pos ()

standardTranslationHasNoFixedX6Point :
  (axis : H.Axis6) →
  (position : H.X6) →
  H.translate axis position ≡ position → ⊥
standardTranslationHasNoFixedX6Point H.axis0 position fixed =
  incrementHasNoFixedPoint (H.x0 position) (cong H.x0 fixed)
standardTranslationHasNoFixedX6Point H.axis1 position fixed =
  incrementHasNoFixedPoint (H.x1 position) (cong H.x1 fixed)
standardTranslationHasNoFixedX6Point H.axis2 position fixed =
  incrementHasNoFixedPoint (H.x2 position) (cong H.x2 fixed)
standardTranslationHasNoFixedX6Point H.axis3 position fixed =
  incrementHasNoFixedPoint (H.x3 position) (cong H.x3 fixed)
standardTranslationHasNoFixedX6Point H.axis4 position fixed =
  incrementHasNoFixedPoint (H.x4 position) (cong H.x4 fixed)
standardTranslationHasNoFixedX6Point H.axis5 position fixed =
  incrementHasNoFixedPoint (H.x5 position) (cong H.x5 fixed)

standardTranslationHasNoFixedModelBasis :
  (axis : H.Axis6) →
  (basis : Model.ZetaModelBasis) →
  Model.translatedBasis axis basis ≡ basis → ⊥
standardTranslationHasNoFixedModelBasis axis basis fixed =
  standardTranslationHasNoFixedX6Point
    axis
    (Model.weightPosition basis)
    (cong Model.weightPosition fixed)

------------------------------------------------------------------------
-- A trace certificate records the exact finite combinatorial producer: the
-- standard basis permutation has no diagonal fixed entries.  Turning this into
-- the full extraspecial character theorem requires the actual E-action and its
-- complete class coverage, not merely the six generators.
------------------------------------------------------------------------

record StandardTranslationTraceCertificate (axis : H.Axis6) : Set where
  constructor standard-translation-trace-certificate
  field
    noFixedBasisVector :
      (basis : Model.ZetaModelBasis) →
      Model.translatedBasis axis basis ≡ basis → ⊥

open StandardTranslationTraceCertificate public

standardTranslationTraceCertificate :
  (axis : H.Axis6) → StandardTranslationTraceCertificate axis
standardTranslationTraceCertificate axis =
  standard-translation-trace-certificate
    (standardTranslationHasNoFixedModelBasis axis)

record ModelStoneVonNeumannBoundary : Set where
  constructor model-stone-von-neumann-boundary
  field
    evaluationMapConstructivelyIsomorphic : Bool
    evaluationMapConstructivelyIsomorphicIsTrue :
      evaluationMapConstructivelyIsomorphic ≡ true

    allSixStandardTranslationsFixedPointFree : Bool
    allSixStandardTranslationsFixedPointFreeIsTrue :
      allSixStandardTranslationsFixedPointFree ≡ true

    actualExtraspecialKernelActionIdentified : Bool
    actualExtraspecialKernelActionIdentifiedIsFalse :
      actualExtraspecialKernelActionIdentified ≡ false

    allNoncentralExtraspecialClassesHaveZeroTrace : Bool
    allNoncentralExtraspecialClassesHaveZeroTraceIsFalse :
      allNoncentralExtraspecialClassesHaveZeroTrace ≡ false

    actualRestrictionIsNinetyHeisenbergCopies : Bool
    actualRestrictionIsNinetyHeisenbergCopiesIsFalse :
      actualRestrictionIsNinetyHeisenbergCopies ≡ false

canonicalModelStoneVonNeumannBoundary : ModelStoneVonNeumannBoundary
canonicalModelStoneVonNeumannBoundary =
  model-stone-von-neumann-boundary
    true refl true refl false refl false refl false refl
