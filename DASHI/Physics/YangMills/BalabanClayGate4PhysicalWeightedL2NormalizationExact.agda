module DASHI.Physics.YangMills.BalabanClayGate4PhysicalWeightedL2NormalizationExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literal finite weighted L2 normalization.
--
-- The adjoint of a linear map between finite-dimensional inner-product spaces
-- is uniquely characterized by
--
--   <Q x, y>_out = <x, Q* y>_in.
--
-- The finite mathematics is standard.  The physical theorem is choosing the
-- fine/coarse volume weights dictated by the CMP 109 convention and proving
-- that the repository's formal transpose satisfies this identity.
------------------------------------------------------------------------

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList function [] = []
mapList function (value ∷ values) =
  function value ∷ mapList function values

finiteSum : ∀ {Scalar : Set} →
  Scalar → (Scalar → Scalar → Scalar) → List Scalar → Scalar
finiteSum zero add [] = zero
finiteSum zero add (value ∷ values) =
  add value (finiteSum zero add values)

record WeightedL2Algebra (Scalar Component : Set) : Set₁ where
  field
    zero : Scalar
    add multiply : Scalar → Scalar → Scalar
    square : Scalar → Scalar
    componentNormSq : Component → Scalar
    Positive : Scalar → Set

open WeightedL2Algebra public

weightedInputNormSq :
  ∀ {Input Scalar Component} →
  WeightedL2Algebra Scalar Component →
  List Input → (Input → Scalar) →
  (Input → Component) → Scalar
weightedInputNormSq algebra inputs weight field =
  finiteSum (zero algebra) (add algebra)
    (mapList
      (λ input →
        multiply algebra
          (square algebra (weight input))
          (componentNormSq algebra (field input)))
      inputs)

weightedOutputNormSq :
  ∀ {Output Scalar Component} →
  WeightedL2Algebra Scalar Component →
  List Output → (Output → Scalar) →
  (Output → Component) → Scalar
weightedOutputNormSq algebra outputs weight field =
  finiteSum (zero algebra) (add algebra)
    (mapList
      (λ output →
        multiply algebra
          (square algebra (weight output))
          (componentNormSq algebra (field output)))
      outputs)

record PhysicalWeightedL2NormMeaning
    (Input Output Scalar Component : Set) : Set₁ where
  field
    algebra : WeightedL2Algebra Scalar Component
    inputElements : List Input
    outputElements : List Output

    inputWeight : Input → Scalar
    outputWeight : Output → Scalar

    inputWeightPositive : ∀ input →
      Positive algebra (inputWeight input)
    outputWeightPositive : ∀ output →
      Positive algebra (outputWeight output)

    physicalInputNormSq : (Input → Component) → Scalar
    physicalOutputNormSq : (Output → Component) → Scalar

    physicalInputNormSqMeaning : ∀ field →
      physicalInputNormSq field
      ≡ weightedInputNormSq algebra inputElements inputWeight field

    physicalOutputNormSqMeaning : ∀ field →
      physicalOutputNormSq field
      ≡ weightedOutputNormSq algebra outputElements outputWeight field

open PhysicalWeightedL2NormMeaning public

record PhysicalAdjointNormalizationMeaning
    (InputField OutputField Scalar : Set) : Set₁ where
  field
    operator : InputField → OutputField
    physicalAdjoint formalTranspose : OutputField → InputField

    inputInner : InputField → InputField → Scalar
    outputInner : OutputField → OutputField → Scalar

    AdjointCharacterization :
      (OutputField → InputField) → Set

    physicalAdjointCharacterization :
      AdjointCharacterization physicalAdjoint

    formalTransposeCharacterization :
      AdjointCharacterization formalTranspose

    characterizationMeaning : ∀ candidate →
      AdjointCharacterization candidate
      ≡ (∀ input output →
          outputInner (operator input) output
          ≡ inputInner input (candidate output))

    adjointUnique : ∀ left right →
      AdjointCharacterization left →
      AdjointCharacterization right →
      left ≡ right

open PhysicalAdjointNormalizationMeaning public

formalTransposeEqualsPhysicalAdjoint :
  ∀ {InputField OutputField Scalar}
    (meaning : PhysicalAdjointNormalizationMeaning
      InputField OutputField Scalar) →
  formalTranspose meaning ≡ physicalAdjoint meaning
formalTransposeEqualsPhysicalAdjoint meaning =
  adjointUnique meaning
    (formalTranspose meaning)
    (physicalAdjoint meaning)
    (formalTransposeCharacterization meaning)
    (physicalAdjointCharacterization meaning)

literalFiniteWeightedL2NormLevel : ProofLevel
literalFiniteWeightedL2NormLevel = computed

physicalWeightedL2MeaningAssemblyLevel : ProofLevel
physicalWeightedL2MeaningAssemblyLevel = machineChecked

formalTransposePhysicalAdjointUniquenessLevel : ProofLevel
formalTransposePhysicalAdjointUniquenessLevel = machineChecked

physicalCMP109FineCoarseWeightInputsLevel : ProofLevel
physicalCMP109FineCoarseWeightInputsLevel = conditional

physicalInnerProductScalingInputsLevel : ProofLevel
physicalInnerProductScalingInputsLevel = conditional

physicalFormalTransposeCharacterizationInputsLevel : ProofLevel
physicalFormalTransposeCharacterizationInputsLevel = conditional
