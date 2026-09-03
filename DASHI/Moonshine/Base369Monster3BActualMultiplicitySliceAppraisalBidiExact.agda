module DASHI.Moonshine.Base369Monster3BActualMultiplicitySliceAppraisalBidiExact where

------------------------------------------------------------------------
-- ACTUAL ZETA RECOGNITION -> ACTUAL 729 APPRAISAL SLICE
--
-- Once ActualZetaSectorRecognition is supplied, the 729 appraisal/Heisenberg
-- bridge is not a second scientific recognition problem.  The actual zeta
-- sector already has literal coordinates
--
--   X6 x Fin 90.
--
-- Fixing one multiplicity coordinate therefore gives a canonical 729-state
-- slice.  The existing Base369 appraisal <-> X6 chart evaluates that slice
-- into the SAME actual zeta sector.  Translation and modulation-exponent laws
-- are compiler consequences of the original recognition.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (Fin)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Moonshine.Base369AppraisalFibreHeisenbergCarrierBidiExact as Carrier
import DASHI.Moonshine.Base369HeisenbergTranslationGridObstructionExact as AppraisalAction
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteProjectorModelExact as Model
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Recognition

------------------------------------------------------------------------
-- 1. Evaluate one Base369 appraisal point into one fixed actual multiplicity
--    slice of the recognized zeta sector.
------------------------------------------------------------------------

actualStateAtAppraisal :
  ∀ {ActualSector : Set} →
  Recognition.ActualZetaSectorRecognition ActualSector →
  Fin 90 →
  Geometry.AppraisalFibrePoint →
  ActualSector
actualStateAtAppraisal recognition multiplicity point =
  Recognition.fromModel recognition
    (Recognition.evaluateModelTensor
      (Carrier.appraisalFibreToX6 point , multiplicity))

actualStateAtAppraisalToModel :
  ∀ {ActualSector : Set} →
  (recognition : Recognition.ActualZetaSectorRecognition ActualSector) →
  (multiplicity : Fin 90) →
  (point : Geometry.AppraisalFibrePoint) →
  Recognition.toModel recognition
    (actualStateAtAppraisal recognition multiplicity point)
  ≡ Recognition.evaluateModelTensor
      (Carrier.appraisalFibreToX6 point , multiplicity)
actualStateAtAppraisalToModel recognition multiplicity point =
  Recognition.toAfterFrom recognition
    (Recognition.evaluateModelTensor
      (Carrier.appraisalFibreToX6 point , multiplicity))

actualStateAtAppraisalWeight :
  ∀ {ActualSector : Set} →
  (recognition : Recognition.ActualZetaSectorRecognition ActualSector) →
  (multiplicity : Fin 90) →
  (point : Geometry.AppraisalFibrePoint) →
  Recognition.actualWeightPosition recognition
    (actualStateAtAppraisal recognition multiplicity point)
  ≡ Carrier.appraisalFibreToX6 point
actualStateAtAppraisalWeight recognition multiplicity point
  rewrite actualStateAtAppraisalToModel recognition multiplicity point = refl

actualStateAtAppraisalMultiplicity :
  ∀ {ActualSector : Set} →
  (recognition : Recognition.ActualZetaSectorRecognition ActualSector) →
  (multiplicity : Fin 90) →
  (point : Geometry.AppraisalFibrePoint) →
  Recognition.actualMultiplicityCoordinate recognition
    (actualStateAtAppraisal recognition multiplicity point)
  ≡ multiplicity
actualStateAtAppraisalMultiplicity recognition multiplicity point
  rewrite actualStateAtAppraisalToModel recognition multiplicity point = refl

------------------------------------------------------------------------
-- 2. The model coordinates separate actual states because recognition is a
--    two-sided isomorphism.
------------------------------------------------------------------------

sameModelCoordinateImpliesSameActualState :
  ∀ {ActualSector : Set}
    {left right : ActualSector} →
  (recognition : Recognition.ActualZetaSectorRecognition ActualSector) →
  Recognition.toModel recognition left
  ≡ Recognition.toModel recognition right →
  left ≡ right
sameModelCoordinateImpliesSameActualState {left = left} {right = right}
  recognition modelEquality =
  trans
    (sym (Recognition.fromAfterTo recognition left))
    (trans
      (cong (Recognition.fromModel recognition) modelEquality)
      (Recognition.fromAfterTo recognition right))

actualStateAtAppraisalInjective :
  ∀ {ActualSector : Set} →
  (recognition : Recognition.ActualZetaSectorRecognition ActualSector) →
  (multiplicity : Fin 90) →
  {left right : Geometry.AppraisalFibrePoint} →
  actualStateAtAppraisal recognition multiplicity left
  ≡ actualStateAtAppraisal recognition multiplicity right →
  left ≡ right
actualStateAtAppraisalInjective recognition multiplicity {left} {right}
  stateEquality =
  trans
    (sym (Carrier.appraisalFibreRoundTrip left))
    (trans
      (cong Carrier.x6ToAppraisalFibre weightEquality)
      (Carrier.appraisalFibreRoundTrip right))
  where
  weightEquality :
    Carrier.appraisalFibreToX6 left ≡ Carrier.appraisalFibreToX6 right
  weightEquality =
    trans
      (sym (actualStateAtAppraisalWeight recognition multiplicity left))
      (trans
        (cong (Recognition.actualWeightPosition recognition) stateEquality)
        (actualStateAtAppraisalWeight recognition multiplicity right))

------------------------------------------------------------------------
-- 3. Every actual state already carrying the selected multiplicity coordinate
--    is recovered by its actual X6 weight and the Base369 inverse chart.
------------------------------------------------------------------------

modelRebuildAtMultiplicity :
  ∀ {ActualSector : Set} →
  (recognition : Recognition.ActualZetaSectorRecognition ActualSector) →
  (multiplicity : Fin 90) →
  (state : ActualSector) →
  Recognition.actualMultiplicityCoordinate recognition state ≡ multiplicity →
  Recognition.toModel recognition state
  ≡ Recognition.evaluateModelTensor
      (Recognition.actualWeightPosition recognition state , multiplicity)
modelRebuildAtMultiplicity recognition multiplicity state multiplicityProof
  with Recognition.toModel recognition state
... | Model.zetaBasis position actualMultiplicity
  rewrite multiplicityProof = refl

actualStateRecoveredFromAppraisal :
  ∀ {ActualSector : Set} →
  (recognition : Recognition.ActualZetaSectorRecognition ActualSector) →
  (multiplicity : Fin 90) →
  (state : ActualSector) →
  Recognition.actualMultiplicityCoordinate recognition state ≡ multiplicity →
  state ≡
    actualStateAtAppraisal recognition multiplicity
      (Carrier.x6ToAppraisalFibre
        (Recognition.actualWeightPosition recognition state))
actualStateRecoveredFromAppraisal recognition multiplicity state multiplicityProof =
  sameModelCoordinateImpliesSameActualState recognition modelEquality
  where
  modelEquality :
    Recognition.toModel recognition state
    ≡ Recognition.toModel recognition
        (actualStateAtAppraisal recognition multiplicity
          (Carrier.x6ToAppraisalFibre
            (Recognition.actualWeightPosition recognition state)))
  modelEquality
    rewrite modelRebuildAtMultiplicity
              recognition multiplicity state multiplicityProof
          | actualStateAtAppraisalToModel recognition multiplicity
              (Carrier.x6ToAppraisalFibre
                (Recognition.actualWeightPosition recognition state))
          | Carrier.x6RoundTrip
              (Recognition.actualWeightPosition recognition state) = refl

------------------------------------------------------------------------
-- 4. Actual translations on the recognized zeta sector are exactly the
--    transported cyclic appraisal action on every fixed multiplicity slice.
------------------------------------------------------------------------

actualAppraisalTranslationModelEquality :
  ∀ {ActualSector : Set} →
  (recognition : Recognition.ActualZetaSectorRecognition ActualSector) →
  (multiplicity : Fin 90) →
  (axis : H.Axis6) →
  (point : Geometry.AppraisalFibrePoint) →
  Recognition.toModel recognition
    (Recognition.actualTranslate recognition axis
      (actualStateAtAppraisal recognition multiplicity point))
  ≡ Recognition.toModel recognition
      (actualStateAtAppraisal recognition multiplicity
        (AppraisalAction.heisenbergTranslateFibre axis point))
actualAppraisalTranslationModelEquality recognition multiplicity axis point
  rewrite Recognition.translationIntertwines recognition axis
            (actualStateAtAppraisal recognition multiplicity point)
        | actualStateAtAppraisalToModel recognition multiplicity point
        | actualStateAtAppraisalToModel recognition multiplicity
            (AppraisalAction.heisenbergTranslateFibre axis point)
        | AppraisalAction.heisenbergTranslateIntertwinesByConstruction
            axis point = refl

actualAppraisalTranslationIntertwines :
  ∀ {ActualSector : Set} →
  (recognition : Recognition.ActualZetaSectorRecognition ActualSector) →
  (multiplicity : Fin 90) →
  (axis : H.Axis6) →
  (point : Geometry.AppraisalFibrePoint) →
  Recognition.actualTranslate recognition axis
    (actualStateAtAppraisal recognition multiplicity point)
  ≡ actualStateAtAppraisal recognition multiplicity
      (AppraisalAction.heisenbergTranslateFibre axis point)
actualAppraisalTranslationIntertwines recognition multiplicity axis point =
  sameModelCoordinateImpliesSameActualState recognition
    (actualAppraisalTranslationModelEquality
      recognition multiplicity axis point)

------------------------------------------------------------------------
-- 5. Actual modulation observers also agree with the same appraisal/X6 state.
------------------------------------------------------------------------

actualAppraisalModulationExponentIntertwines :
  ∀ {ActualSector : Set} →
  (recognition : Recognition.ActualZetaSectorRecognition ActualSector) →
  (multiplicity : Fin 90) →
  (axis : H.Axis6) →
  (point : Geometry.AppraisalFibrePoint) →
  Recognition.actualModulationExponent recognition axis
    (actualStateAtAppraisal recognition multiplicity point)
  ≡ H.modulationExponent axis (Carrier.appraisalFibreToX6 point)
actualAppraisalModulationExponentIntertwines recognition multiplicity axis point
  rewrite Recognition.modulationExponentIntertwines recognition axis
            (actualStateAtAppraisal recognition multiplicity point)
        | actualStateAtAppraisalToModel recognition multiplicity point = refl

------------------------------------------------------------------------
-- 6. BIDI consequence: after actual zeta recognition, the 729 action bridge is
--    generated for every literal Fin 90 slice.  No separate cardinality-first
--    representation search remains.
------------------------------------------------------------------------

record ActualMultiplicitySliceAppraisalBoundary : Set where
  constructor actual-multiplicity-slice-appraisal-boundary
  field
    actualRecognitionProvidesX6TimesFin90 : Bool
    fixedMultiplicitySliceEvaluatedIntoActualSector : Bool
    appraisalEvaluationInjective : Bool
    everyStateInSelectedMultiplicityRecovered : Bool
    actualTranslationIntertwinesAppraisal : Bool
    actualModulationObserverIntertwinesAppraisal : Bool
    separate729CarrierRecognitionNeededAfterZetaRecognition : Bool
    actualZetaRecognitionInhabitedHere : Bool

canonicalActualMultiplicitySliceAppraisalBoundary :
  ActualMultiplicitySliceAppraisalBoundary
canonicalActualMultiplicitySliceAppraisalBoundary =
  actual-multiplicity-slice-appraisal-boundary
    true true true true true true false false
