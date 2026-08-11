module DASHI.Moonshine.Monster3BMultiplicityEvaluationExact where

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
-- R. W. Barraclough and R. A. Wilson,
-- "The Character Table of a Maximal Subgroup of the Monster",
-- LMS Journal of Computation and Mathematics 10 (2007), 161--175.
-- DOI: 10.1112/S1461157000001352.
--
-- DASHI CONTRIBUTION
--
-- Make the model multiplicity space literal:
--
--   H_model = F_3^6,
--   S_model = Fin 90,
--   H_model x S_model ~= ZetaModelBasis.
--
-- Each multiplicity coordinate gives a translation-equivariant embedding of
-- the Schrodinger basis.  One actual-sector recognition isomorphism now
-- retains both the six translations and the six modulation-exponent observers.
-- From those inputs all 36 standard Weyl exponent relations, projector
-- transport, and translation fixed-point-freedom are derived.  This minimizes
-- the remaining promotion input without pretending it has already been
-- supplied by the actual Monster representation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import DASHI.Algebra.Trit using (Trit)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteProjectorModelExact as Model
import DASHI.Moonshine.Monster3BFiniteWeightProjectorExact as Projector
import DASHI.Moonshine.Monster3BModelProjectorResolutionExact as Resolution
import DASHI.Moonshine.Monster3BModelStoneVonNeumannRecognitionExact as Stone

ModelHeisenbergBasis : Set
ModelHeisenbergBasis = H.X6

ModelMultiplicitySpace : Set
ModelMultiplicitySpace = Fin 90

ModelTensorBasis : Set
ModelTensorBasis = ModelHeisenbergBasis × ModelMultiplicitySpace

evaluateModelTensor : ModelTensorBasis → Model.ZetaModelBasis
evaluateModelTensor (position , multiplicity) =
  Model.zetaBasis position multiplicity

recoverModelTensor : Model.ZetaModelBasis → ModelTensorBasis
recoverModelTensor basis =
  Model.weightPosition basis , Model.multiplicityCoordinate basis

recoverAfterEvaluate :
  (tensor : ModelTensorBasis) →
  recoverModelTensor (evaluateModelTensor tensor) ≡ tensor
recoverAfterEvaluate (position , multiplicity) = refl

evaluateAfterRecover :
  (basis : Model.ZetaModelBasis) →
  evaluateModelTensor (recoverModelTensor basis) ≡ basis
evaluateAfterRecover (Model.zetaBasis position multiplicity) = refl

multiplicityEmbedding :
  ModelMultiplicitySpace → ModelHeisenbergBasis → Model.ZetaModelBasis
multiplicityEmbedding multiplicity position =
  Model.zetaBasis position multiplicity

multiplicityEmbeddingTranslationEquivariant :
  (multiplicity : ModelMultiplicitySpace) →
  (axis : H.Axis6) →
  (position : ModelHeisenbergBasis) →
  multiplicityEmbedding multiplicity (H.translate axis position)
  ≡ Model.translatedBasis axis
      (multiplicityEmbedding multiplicity position)
multiplicityEmbeddingTranslationEquivariant multiplicity axis position = refl

multiplicityEmbeddingModulationExponent :
  (multiplicity : ModelMultiplicitySpace) →
  (axis : H.Axis6) →
  (position : ModelHeisenbergBasis) →
  H.modulationExponent axis
    (Model.weightPosition (multiplicityEmbedding multiplicity position))
  ≡ H.modulationExponent axis position
multiplicityEmbeddingModulationExponent multiplicity axis position = refl

modelHeisenbergDimension : Nat
modelHeisenbergDimension = 729

modelMultiplicityDimension : Nat
modelMultiplicityDimension = 90

modelTensorDimension : Nat
modelTensorDimension = modelHeisenbergDimension * modelMultiplicityDimension

modelTensorDimensionIs65610 : modelTensorDimension ≡ 65610
modelTensorDimensionIs65610 = refl

record ModelMultiplicityEvaluationIsomorphism : Set where
  constructor model-multiplicity-evaluation-isomorphism
  field
    forward : ModelTensorBasis → Model.ZetaModelBasis
    inverse : Model.ZetaModelBasis → ModelTensorBasis
    inverseAfterForward :
      (tensor : ModelTensorBasis) → inverse (forward tensor) ≡ tensor
    forwardAfterInverse :
      (basis : Model.ZetaModelBasis) → forward (inverse basis) ≡ basis

open ModelMultiplicityEvaluationIsomorphism public

canonicalModelMultiplicityEvaluationIsomorphism :
  ModelMultiplicityEvaluationIsomorphism
canonicalModelMultiplicityEvaluationIsomorphism =
  model-multiplicity-evaluation-isomorphism
    evaluateModelTensor
    recoverModelTensor
    recoverAfterEvaluate
    evaluateAfterRecover

------------------------------------------------------------------------
-- One proof-bearing promotion object replaces a collection of unrelated
-- "actual sector" Booleans.  Translation and modulation are distinct data:
-- the latter records the exponent read by the diagonal Weyl generator.
------------------------------------------------------------------------

record ActualZetaSectorRecognition (ActualSector : Set) : Set where
  constructor actual-zeta-sector-recognition
  field
    toModel : ActualSector → Model.ZetaModelBasis
    fromModel : Model.ZetaModelBasis → ActualSector
    fromAfterTo : (state : ActualSector) → fromModel (toModel state) ≡ state
    toAfterFrom :
      (basis : Model.ZetaModelBasis) → toModel (fromModel basis) ≡ basis

    actualTranslate : H.Axis6 → ActualSector → ActualSector
    translationIntertwines :
      (axis : H.Axis6) →
      (state : ActualSector) →
      toModel (actualTranslate axis state)
      ≡ Model.translatedBasis axis (toModel state)

    actualModulationExponent : H.Axis6 → ActualSector → Trit
    modulationExponentIntertwines :
      (axis : H.Axis6) →
      (state : ActualSector) →
      actualModulationExponent axis state
      ≡ H.modulationExponent axis
          (Model.weightPosition (toModel state))

open ActualZetaSectorRecognition public

actualWeightPosition :
  ∀ {ActualSector} →
  ActualZetaSectorRecognition ActualSector →
  ActualSector → H.X6
actualWeightPosition recognition state =
  Model.weightPosition (toModel recognition state)

actualMultiplicityCoordinate :
  ∀ {ActualSector} →
  ActualZetaSectorRecognition ActualSector →
  ActualSector → Fin 90
actualMultiplicityCoordinate recognition state =
  Model.multiplicityCoordinate (toModel recognition state)

actualWeightProjectorCoefficient :
  ∀ {ActualSector} →
  ActualZetaSectorRecognition ActualSector →
  H.X6 → ActualSector → Nat
actualWeightProjectorCoefficient recognition selected state =
  Projector.weightProjectorCoefficient selected (toModel recognition state)

actualOwnWeightProjectorCoefficient :
  ∀ {ActualSector} →
  (recognition : ActualZetaSectorRecognition ActualSector) →
  (state : ActualSector) →
  actualWeightProjectorCoefficient recognition
    (actualWeightPosition recognition state) state
  ≡ 1
actualOwnWeightProjectorCoefficient recognition state =
  Resolution.projectorCoefficientOnOwnWeight (toModel recognition state)

actualProjectorTranslationCovariant :
  ∀ {ActualSector} →
  (recognition : ActualZetaSectorRecognition ActualSector) →
  (axis : H.Axis6) →
  (selected : H.X6) →
  (state : ActualSector) →
  actualWeightProjectorCoefficient recognition
    (H.translate axis selected)
    (actualTranslate recognition axis state)
  ≡ actualWeightProjectorCoefficient recognition selected state
actualProjectorTranslationCovariant recognition axis selected state
  rewrite translationIntertwines recognition axis state =
  Resolution.projectorResolutionTranslationCovariant
    axis selected (toModel recognition state)

actualGeneratorWeylExponent :
  ∀ {ActualSector} →
  (recognition : ActualZetaSectorRecognition ActualSector) →
  (dual translationAxis : H.Axis6) →
  (state : ActualSector) →
  actualModulationExponent recognition dual
    (actualTranslate recognition translationAxis state)
  ≡ H._+3_
      (H.kronecker dual translationAxis)
      (actualModulationExponent recognition dual state)
actualGeneratorWeylExponent recognition dual translationAxis state
  rewrite modulationExponentIntertwines recognition dual
            (actualTranslate recognition translationAxis state)
        | translationIntertwines recognition translationAxis state
        | modulationExponentIntertwines recognition dual state =
  H.generatorWeylExponent
    dual translationAxis
    (Model.weightPosition (toModel recognition state))

actualStandardTranslationFixedPointFree :
  ∀ {ActualSector} →
  (recognition : ActualZetaSectorRecognition ActualSector) →
  (axis : H.Axis6) →
  (state : ActualSector) →
  actualTranslate recognition axis state ≡ state → ⊥
actualStandardTranslationFixedPointFree recognition axis state fixed =
  Stone.standardTranslationHasNoFixedModelBasis
    axis
    (toModel recognition state)
    (trans
      (sym (translationIntertwines recognition axis state))
      (cong (toModel recognition) fixed))

record MultiplicityPromotionBoundary : Set where
  constructor multiplicity-promotion-boundary
  field
    modelEvaluationRoundTrip :
      (tensor : ModelTensorBasis) →
      recoverModelTensor (evaluateModelTensor tensor) ≡ tensor
    modelDimensionWitness : modelTensorDimension ≡ 65610
    actualMonsterRecognitionConstructed : Bool
    actualMonsterRecognitionConstructedIsFalse :
      actualMonsterRecognitionConstructed ≡ false
    actualKernelClassCharacterCertified : Bool
    actualKernelClassCharacterCertifiedIsFalse :
      actualKernelClassCharacterCertified ≡ false
    actualWeylGeneratorRecognitionConstructed : Bool
    actualWeylGeneratorRecognitionConstructedIsFalse :
      actualWeylGeneratorRecognitionConstructed ≡ false

canonicalMultiplicityPromotionBoundary : MultiplicityPromotionBoundary
canonicalMultiplicityPromotionBoundary =
  multiplicity-promotion-boundary
    recoverAfterEvaluate
    modelTensorDimensionIs65610
    false refl
    false refl
    false refl
