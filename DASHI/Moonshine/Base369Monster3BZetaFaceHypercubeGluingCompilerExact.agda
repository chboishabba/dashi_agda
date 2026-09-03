module DASHI.Moonshine.Base369Monster3BZetaFaceHypercubeGluingCompilerExact where

------------------------------------------------------------------------
-- ACTUAL ZETA RECOGNITION -> FACE-HYPERCUBE GLUING COMPILER
--
-- ActualZetaSectorRecognition already owns a two-sided actual-sector chart
--
--   ActualSector <-> X6 x Fin 90
--
-- together with the six actual translated X6 generators.  Fixing one
-- multiplicity m therefore embeds ONE literal X6 slice in ActualSector.
--
-- All six geometric face charts may reuse that same slice.  Taking identity
-- transition maps on the model side then makes all 12 edge agreements and all
-- 8 corner cocycles compiler output.  This prunes a separate face-gluing
-- theorem AFTER zeta recognition.  It does NOT identify the six translations
-- with the full Monster normalizer action, and it does not construct zeta
-- recognition itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (Fin)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27BoundaryNerveExact as Nerve
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Recognition
import DASHI.Moonshine.Base369Monster3BActualMultiplicitySliceAppraisalBidiExact as Slice
import DASHI.Moonshine.Base369Ternary27FaceHypercubeCechGluingBidiExact as Cech

------------------------------------------------------------------------
-- 1. Canonical fixed-multiplicity X6 inclusion into the actual zeta sector.
------------------------------------------------------------------------

includeAtMultiplicity :
  ∀ {ActualSector : Set} →
  Recognition.ActualZetaSectorRecognition ActualSector →
  Fin 90 →
  H.X6 →
  ActualSector
includeAtMultiplicity recognition multiplicity state =
  Recognition.fromModel recognition
    (Recognition.evaluateModelTensor (state , multiplicity))

includeAtMultiplicityToModel :
  ∀ {ActualSector : Set} →
  (recognition : Recognition.ActualZetaSectorRecognition ActualSector) →
  (multiplicity : Fin 90) →
  (state : H.X6) →
  Recognition.toModel recognition
    (includeAtMultiplicity recognition multiplicity state)
  ≡ Recognition.evaluateModelTensor (state , multiplicity)
includeAtMultiplicityToModel recognition multiplicity state =
  Recognition.toAfterFrom recognition
    (Recognition.evaluateModelTensor (state , multiplicity))

includeAtMultiplicityWeight :
  ∀ {ActualSector : Set} →
  (recognition : Recognition.ActualZetaSectorRecognition ActualSector) →
  (multiplicity : Fin 90) →
  (state : H.X6) →
  Recognition.actualWeightPosition recognition
    (includeAtMultiplicity recognition multiplicity state)
  ≡ state
includeAtMultiplicityWeight recognition multiplicity state
  rewrite includeAtMultiplicityToModel recognition multiplicity state = refl

includeAtMultiplicityInjective :
  ∀ {ActualSector : Set} →
  (recognition : Recognition.ActualZetaSectorRecognition ActualSector) →
  (multiplicity : Fin 90) →
  {left right : H.X6} →
  includeAtMultiplicity recognition multiplicity left
  ≡ includeAtMultiplicity recognition multiplicity right →
  left ≡ right
includeAtMultiplicityInjective recognition multiplicity {left} {right} equality =
  trans
    (sym (includeAtMultiplicityWeight recognition multiplicity left))
    (trans
      (cong (Recognition.actualWeightPosition recognition) equality)
      (includeAtMultiplicityWeight recognition multiplicity right))

------------------------------------------------------------------------
-- 2. The actual recognized translations preserve every selected slice.
------------------------------------------------------------------------

includeTranslationIntertwines :
  ∀ {ActualSector : Set} →
  (recognition : Recognition.ActualZetaSectorRecognition ActualSector) →
  (multiplicity : Fin 90) →
  (axis : H.Axis6) →
  (state : H.X6) →
  includeAtMultiplicity recognition multiplicity (H.translate axis state)
  ≡ Recognition.actualTranslate recognition axis
      (includeAtMultiplicity recognition multiplicity state)
includeTranslationIntertwines recognition multiplicity axis state =
  Slice.sameModelCoordinateImpliesSameActualState recognition modelEquality
  where
  modelEquality :
    Recognition.toModel recognition
      (includeAtMultiplicity recognition multiplicity (H.translate axis state))
    ≡ Recognition.toModel recognition
        (Recognition.actualTranslate recognition axis
          (includeAtMultiplicity recognition multiplicity state))
  modelEquality
    rewrite includeAtMultiplicityToModel recognition multiplicity
              (H.translate axis state)
          | Recognition.translationIntertwines recognition axis
              (includeAtMultiplicity recognition multiplicity state)
          | includeAtMultiplicityToModel recognition multiplicity state = refl

------------------------------------------------------------------------
-- 3. Compile the Cech gluing promotion.  Actor here is Axis6: this is the
--    recognized Heisenberg translation action, not the whole Monster group.
------------------------------------------------------------------------

zetaFaceHypercubeGluing :
  ∀ {ActualSector : Set} →
  (recognition : Recognition.ActualZetaSectorRecognition ActualSector) →
  (multiplicity : Fin 90) →
  Cech.ActualFaceHypercubeGluingPromotion H.Axis6 ActualSector
zetaFaceHypercubeGluing recognition multiplicity = record
  { modelGluing = Cech.uniformModelGluing H.translate
  ; actualAct = Recognition.actualTranslate recognition
  ; includeFace = λ face state →
      includeAtMultiplicity recognition multiplicity state
  ; includeFaceInjective = λ face equality →
      includeAtMultiplicityInjective recognition multiplicity equality
  ; includeFaceIntertwines = λ face axis state →
      includeTranslationIntertwines recognition multiplicity axis state
  ; edgeDescriptionsAgreeInActualState = λ edge state → refl
  }

------------------------------------------------------------------------
-- 4. Exact pruning boundary.
------------------------------------------------------------------------

record ZetaFaceGluingCompilerBoundary : Set where
  constructor zetaFaceGluingCompilerBoundary
  field
    zetaRecognitionProvidesLiteralX6TimesFin90 : Bool
    fixedMultiplicityProvidesOneActualX6Slice : Bool
    sixFaceChartsReuseSameActualSlice : Bool
    twelveEdgeAgreementsGenerated : Bool
    eightCornerCocyclesGenerated : Bool
    sixActualTranslationIntertwinersReused : Bool
    separateFaceGluingTheoremNeededAfterZetaRecognition : Bool
    fullMonsterNormalizerGluingConstructedHere : Bool
    actualZetaRecognitionConstructedHere : Bool

canonicalZetaFaceGluingCompilerBoundary : ZetaFaceGluingCompilerBoundary
canonicalZetaFaceGluingCompilerBoundary =
  zetaFaceGluingCompilerBoundary true true true true true true false false false
