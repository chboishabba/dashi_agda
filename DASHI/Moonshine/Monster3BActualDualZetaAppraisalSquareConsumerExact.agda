module DASHI.Moonshine.Monster3BActualDualZetaAppraisalSquareConsumerExact where

------------------------------------------------------------------------
-- Compose existing ZETA commuting square with the actual source inverter.
-- OWNERS: Monster3BCentralCharacterInertiaExact,
-- Monster3BMultiplicityEvaluationExact,
-- Base369Monster3BActualMultiplicitySliceAppraisalBidiExact.
-- No new appraisal carrier, assumption-free Monster action or IIT proof.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Fin.Base using (Fin)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Moonshine.Monster3BCentralCharacterInertiaExact as Inertia
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Recognition
import DASHI.Moonshine.Monster3BFiniteProjectorModelExact as Model
import DASHI.Moonshine.Base369AppraisalFibreHeisenbergCarrierBidiExact as Carrier
import DASHI.Moonshine.Base369Monster3BActualMultiplicitySliceAppraisalBidiExact as Slice

-- This is an EXPLICIT source-premise record. No instance for actual
-- Monster normalizer action/selected 6.Suz representation is supplied.
record DualZetaActualAppraisalSquareInput : Set₁ where
  field
    State Normalizer : Set
    action : Inertia.CentralNormalizerAction State Normalizer
    centreInverter : Inertia.CentralInverter action

    plusRecognition :
      Recognition.ActualZetaSectorRecognition
        (Inertia.CentralEigenspace
          (Inertia.phaseAction action) Inertia.phaseZeta)
    minusRecognition :
      Recognition.ActualZetaSectorRecognition
        (Inertia.CentralEigenspace
          (Inertia.phaseAction action) Inertia.phaseZetaSquared)

    mirrorPoint : Geometry.AppraisalFibrePoint → Geometry.AppraisalFibrePoint
    mirrorMultiplicity : Fin 90 → Fin 90
    mirrorModel : Model.ZetaModelBasis → Model.ZetaModelBasis

    -- Required actual source-word/model compatibility, not discharged by
    -- the finite 1458 model nor by any source-class character fingerprint.
    actualModelMirrorSquare :
      (state : Inertia.CentralEigenspace
        (Inertia.phaseAction action) Inertia.phaseZeta) →
      Recognition.toModel minusRecognition
        (Inertia.inverterSendsZetaToZetaSquared action centreInverter state)
      ≡ mirrorModel (Recognition.toModel plusRecognition state)

    -- Required original appraisal-basis/source-word compatibility.
    modelAppraisalMirrorSquare :
      (multiplicity : Fin 90) →
      (point : Geometry.AppraisalFibrePoint) →
      mirrorModel
        (Recognition.evaluateModelTensor
          (Carrier.appraisalFibreToX6 point , multiplicity))
      ≡ Recognition.evaluateModelTensor
          (Carrier.appraisalFibreToX6 (mirrorPoint point) ,
           mirrorMultiplicity multiplicity)

open DualZetaActualAppraisalSquareInput public

modelCoordinateSquare :
  (input : DualZetaActualAppraisalSquareInput) →
  (multiplicity : Fin 90) →
  (point : Geometry.AppraisalFibrePoint) →
  Recognition.toModel (minusRecognition input)
    (Inertia.inverterSendsZetaToZetaSquared
      (action input) (centreInverter input)
      (Slice.actualStateAtAppraisal
        (plusRecognition input) multiplicity point))
  ≡ Recognition.toModel (minusRecognition input)
      (Slice.actualStateAtAppraisal
        (minusRecognition input)
        (mirrorMultiplicity input multiplicity)
        (mirrorPoint input point))
modelCoordinateSquare input multiplicity point =
  trans
    (actualModelMirrorSquare input
      (Slice.actualStateAtAppraisal
        (plusRecognition input) multiplicity point))
    (trans
      (cong (mirrorModel input)
        (Slice.actualStateAtAppraisalToModel
          (plusRecognition input) multiplicity point))
      (trans
        (modelAppraisalMirrorSquare input multiplicity point)
        (sym (Slice.actualStateAtAppraisalToModel
          (minusRecognition input)
          (mirrorMultiplicity input multiplicity)
          (mirrorPoint input point)))))

-- Existing BIDI injectivity upgrades model-coordinate commutation to
-- literal actual-state commutation, CONDITIONAL on the record above.
actualStateSquare :
  (input : DualZetaActualAppraisalSquareInput) →
  (multiplicity : Fin 90) →
  (point : Geometry.AppraisalFibrePoint) →
  Inertia.inverterSendsZetaToZetaSquared
    (action input) (centreInverter input)
    (Slice.actualStateAtAppraisal
      (plusRecognition input) multiplicity point)
  ≡ Slice.actualStateAtAppraisal
      (minusRecognition input)
      (mirrorMultiplicity input multiplicity)
      (mirrorPoint input point)
actualStateSquare input multiplicity point =
  Slice.sameModelCoordinateImpliesSameActualState
    (minusRecognition input)
    (modelCoordinateSquare input multiplicity point)
