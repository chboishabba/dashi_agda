module DASHI.Moonshine.Monster3BActualMultiplicityEvaluationFromRecognitionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- I. M. Isaacs,
-- "Character Theory of Finite Groups",
-- Dover Publications, 1994 reprint of the 1976 edition.
-- ISBN: 978-0-486-68014-9; no DOI assigned.
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- DASHI CONTRIBUTION
--
-- Upgrade the existing ActualZetaSectorRecognition owner to the literal
-- multiplicity-space evaluation theorem.  No second actual-sector interface is
-- introduced.  The actual map H_model x Fin 90 -> W_zeta is the composite of
-- the concrete model evaluation with the supplied recognition inverse, and
-- its inverse is constructed by the opposite composite.  Both round trips and
-- translation equivariance are derived.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteProjectorModelExact as Model
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Existing

------------------------------------------------------------------------
-- Tensor-basis translation acts on the Heisenberg coordinate only.
------------------------------------------------------------------------

translateModelTensor :
  H.Axis6 → Existing.ModelTensorBasis → Existing.ModelTensorBasis
translateModelTensor axis (position , multiplicity) =
  H.translate axis position , multiplicity

modelEvaluationTranslationEquivariant :
  (axis : H.Axis6) →
  (tensor : Existing.ModelTensorBasis) →
  Existing.evaluateModelTensor (translateModelTensor axis tensor)
  ≡ Model.translatedBasis axis (Existing.evaluateModelTensor tensor)
modelEvaluationTranslationEquivariant axis (position , multiplicity) = refl

------------------------------------------------------------------------
-- Actual evaluation map obtained from the single stronger recognition owner.
------------------------------------------------------------------------

actualEvaluationMap :
  ∀ {ActualSector} →
  Existing.ActualZetaSectorRecognition ActualSector →
  Existing.ModelTensorBasis → ActualSector
actualEvaluationMap recognition tensor =
  Existing.fromModel recognition (Existing.evaluateModelTensor tensor)

actualEvaluationInverse :
  ∀ {ActualSector} →
  Existing.ActualZetaSectorRecognition ActualSector →
  ActualSector → Existing.ModelTensorBasis
actualEvaluationInverse recognition state =
  Existing.recoverModelTensor (Existing.toModel recognition state)

actualEvaluationLeftInverse :
  ∀ {ActualSector} →
  (recognition : Existing.ActualZetaSectorRecognition ActualSector) →
  (tensor : Existing.ModelTensorBasis) →
  actualEvaluationInverse recognition
    (actualEvaluationMap recognition tensor)
  ≡ tensor
actualEvaluationLeftInverse recognition tensor =
  trans
    (cong Existing.recoverModelTensor
      (Existing.toAfterFrom recognition
        (Existing.evaluateModelTensor tensor)))
    (Existing.recoverAfterEvaluate tensor)

actualEvaluationRightInverse :
  ∀ {ActualSector} →
  (recognition : Existing.ActualZetaSectorRecognition ActualSector) →
  (state : ActualSector) →
  actualEvaluationMap recognition
    (actualEvaluationInverse recognition state)
  ≡ state
actualEvaluationRightInverse recognition state =
  trans
    (cong (Existing.fromModel recognition)
      (Existing.evaluateAfterRecover
        (Existing.toModel recognition state)))
    (Existing.fromAfterTo recognition state)

actualEvaluationTranslationEquivariant :
  ∀ {ActualSector} →
  (recognition : Existing.ActualZetaSectorRecognition ActualSector) →
  (axis : H.Axis6) →
  (tensor : Existing.ModelTensorBasis) →
  actualEvaluationMap recognition (translateModelTensor axis tensor)
  ≡ Existing.actualTranslate recognition axis
      (actualEvaluationMap recognition tensor)
actualEvaluationTranslationEquivariant recognition axis tensor =
  Existing.actualEvaluationMapInjectiveViaModel
  where
    actualEvaluationMapInjectiveViaModel :
      Existing.fromModel recognition
        (Existing.evaluateModelTensor (translateModelTensor axis tensor))
      ≡ Existing.actualTranslate recognition axis
          (Existing.fromModel recognition
            (Existing.evaluateModelTensor tensor))
    actualEvaluationMapInjectiveViaModel =
      let
        modelStep :
          Existing.toModel recognition
            (Existing.fromModel recognition
              (Existing.evaluateModelTensor
                (translateModelTensor axis tensor)))
          ≡ Existing.toModel recognition
              (Existing.actualTranslate recognition axis
                (Existing.fromModel recognition
                  (Existing.evaluateModelTensor tensor)))
        modelStep =
          trans
            (Existing.toAfterFrom recognition
              (Existing.evaluateModelTensor
                (translateModelTensor axis tensor)))
            (trans
              (modelEvaluationTranslationEquivariant axis tensor)
              (trans
                (cong (Model.translatedBasis axis)
                  (symmetry
                    (Existing.toAfterFrom recognition
                      (Existing.evaluateModelTensor tensor))))
                (symmetry
                  (Existing.translationIntertwines recognition axis
                    (Existing.fromModel recognition
                      (Existing.evaluateModelTensor tensor))))))
      in
      trans
        (symmetry
          (Existing.fromAfterTo recognition
            (Existing.fromModel recognition
              (Existing.evaluateModelTensor
                (translateModelTensor axis tensor)))))
        (trans
          (cong (Existing.fromModel recognition) modelStep)
          (Existing.fromAfterTo recognition
            (Existing.actualTranslate recognition axis
              (Existing.fromModel recognition
                (Existing.evaluateModelTensor tensor)))))

symmetry :
  ∀ {A : Set} {left right : A} → left ≡ right → right ≡ left
symmetry refl = refl

------------------------------------------------------------------------
-- Packaged actual isomorphism and immediate coordinate consequences.
------------------------------------------------------------------------

record ActualMultiplicityEvaluationIsomorphism
  (ActualSector : Set) : Set where
  constructor actual-multiplicity-evaluation-isomorphism
  field
    recognition : Existing.ActualZetaSectorRecognition ActualSector
    forward : Existing.ModelTensorBasis → ActualSector
    inverse : ActualSector → Existing.ModelTensorBasis
    inverseAfterForward :
      (tensor : Existing.ModelTensorBasis) →
      inverse (forward tensor) ≡ tensor
    forwardAfterInverse :
      (state : ActualSector) →
      forward (inverse state) ≡ state
    translationEquivariant :
      (axis : H.Axis6) →
      (tensor : Existing.ModelTensorBasis) →
      forward (translateModelTensor axis tensor)
      ≡ Existing.actualTranslate recognition axis (forward tensor)

open ActualMultiplicityEvaluationIsomorphism public

actualMonsterMultiplicityEvaluationIsomorphism :
  ∀ {ActualSector} →
  (recognition : Existing.ActualZetaSectorRecognition ActualSector) →
  ActualMultiplicityEvaluationIsomorphism ActualSector
actualMonsterMultiplicityEvaluationIsomorphism recognition =
  actual-multiplicity-evaluation-isomorphism
    recognition
    (actualEvaluationMap recognition)
    (actualEvaluationInverse recognition)
    (actualEvaluationLeftInverse recognition)
    (actualEvaluationRightInverse recognition)
    (actualEvaluationTranslationEquivariant recognition)

actualMultiplicityCoordinateAfterEvaluation :
  ∀ {ActualSector} →
  (recognition : Existing.ActualZetaSectorRecognition ActualSector) →
  (position : Existing.ModelHeisenbergBasis) →
  (multiplicity : Existing.ModelMultiplicitySpace) →
  Existing.actualMultiplicityCoordinate recognition
    (actualEvaluationMap recognition (position , multiplicity))
  ≡ multiplicity
actualMultiplicityCoordinateAfterEvaluation recognition position multiplicity
  rewrite Existing.toAfterFrom recognition
    (Existing.evaluateModelTensor (position , multiplicity)) = refl

actualWeightPositionAfterEvaluation :
  ∀ {ActualSector} →
  (recognition : Existing.ActualZetaSectorRecognition ActualSector) →
  (position : Existing.ModelHeisenbergBasis) →
  (multiplicity : Existing.ModelMultiplicitySpace) →
  Existing.actualWeightPosition recognition
    (actualEvaluationMap recognition (position , multiplicity))
  ≡ position
actualWeightPositionAfterEvaluation recognition position multiplicity
  rewrite Existing.toAfterFrom recognition
    (Existing.evaluateModelTensor (position , multiplicity)) = refl
