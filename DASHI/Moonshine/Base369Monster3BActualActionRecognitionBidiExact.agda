module DASHI.Moonshine.Base369Monster3BActualActionRecognitionBidiExact where

------------------------------------------------------------------------
-- ACTUAL MN3B ACTION RECOGNITION -> EXISTING PROMOTION COMPILERS
--
-- This owner adds no new Monster representation hypothesis.  It packages the
-- two genuinely live producers already isolated by the repository:
--
--   1. an actual phase-resolved MN3B zeta sector;
--   2. an actual recognition of that same chosen sector as the concrete
--      X6 x Fin 90 Weyl model.
--
-- Everything below is compiler output from already-owned modules.  In
-- particular, neither 65610 = 729 * 90 nor character equality is used as a
-- substitute for an intertwining recognition.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (Fin)
open import Data.Product using (_×_)
open import DASHI.Algebra.Trit using (Trit)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Moonshine.Monster3BCentralCharacterInertiaExact as Inertia
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Actual
import DASHI.Moonshine.Monster3BActualZetaPromotionPipelineExact as Pipeline
import DASHI.Moonshine.Base369Monster3BActualSectorRecognitionBidiExact as Base369
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H

record ActualMonster3BActionRecognition : Set₁ where
  field
    phaseResolved : Inertia.ActualMonster3BPhaseResolvedSector

  open Inertia.ActualMonster3BPhaseResolvedSector phaseResolved public

  field
    recognition : Actual.ActualZetaSectorRecognition chosenZetaSector

open ActualMonster3BActionRecognition public

actualPromotionPipeline :
  ActualMonster3BActionRecognition → Pipeline.ActualZetaPromotionPipeline
actualPromotionPipeline source =
  record
    { phaseResolved = phaseResolved source
    ; modelRecognition = recognition source
    }

actualBase369Recognition :
  (source : ActualMonster3BActionRecognition) →
  Base369.ActualBase369SectorRecognition (chosenZetaSector source)
actualBase369Recognition source =
  Base369.composeActualRecognitionWithBase369 (recognition source)

actualSectorToBase369 :
  (source : ActualMonster3BActionRecognition) →
  chosenZetaSector source →
  Geometry.AppraisalFibrePoint × Fin 90
actualSectorToBase369 source =
  Base369.toBase369 (actualBase369Recognition source)

base369ToActualSector :
  (source : ActualMonster3BActionRecognition) →
  Geometry.AppraisalFibrePoint × Fin 90 →
  chosenZetaSector source
base369ToActualSector source =
  Base369.fromBase369 (actualBase369Recognition source)

actualSectorRoundTrip :
  (source : ActualMonster3BActionRecognition) →
  (state : chosenZetaSector source) →
  base369ToActualSector source (actualSectorToBase369 source state) ≡ state
actualSectorRoundTrip source =
  Base369.fromAfterTo (actualBase369Recognition source)

base369RoundTrip :
  (source : ActualMonster3BActionRecognition) →
  (basis : Geometry.AppraisalFibrePoint × Fin 90) →
  actualSectorToBase369 source (base369ToActualSector source basis) ≡ basis
base369RoundTrip source =
  Base369.toAfterFrom (actualBase369Recognition source)

translationIntertwining :
  (source : ActualMonster3BActionRecognition) →
  (axis : H.Axis6) →
  (state : chosenZetaSector source) →
  actualSectorToBase369 source
    (Actual.actualTranslate (recognition source) axis state)
  ≡ Base369.translateBase369Multiplicity axis
      (actualSectorToBase369 source state)
translationIntertwining source =
  Base369.actualTranslationIntertwinesBase369 (recognition source)

modulationExponentIntertwining :
  (source : ActualMonster3BActionRecognition) →
  (axis : H.Axis6) →
  (state : chosenZetaSector source) →
  Actual.actualModulationExponent (recognition source) axis state
  ≡ Base369.base369ModulationExponent axis
      (Data.Product.proj₁ (actualSectorToBase369 source state))
modulationExponentIntertwining source =
  Base369.actualModulationExponentIntertwinesBase369 (recognition source)

record ActualActionRecognitionBoundary : Set where
  constructor actual-action-recognition-boundary
  field
    promotionPipelineIsCompilerOutput : Bool
    promotionPipelineIsCompilerOutputIsTrue :
      promotionPipelineIsCompilerOutput ≡ true
    base369FibreTimes90IsCompilerOutput : Bool
    base369FibreTimes90IsCompilerOutputIsTrue :
      base369FibreTimes90IsCompilerOutput ≡ true
    translationIntertwiningIsCompilerOutput : Bool
    translationIntertwiningIsCompilerOutputIsTrue :
      translationIntertwiningIsCompilerOutput ≡ true
    modulationIntertwiningIsCompilerOutput : Bool
    modulationIntertwiningIsCompilerOutputIsTrue :
      modulationIntertwiningIsCompilerOutput ≡ true
    actualActionRecognitionInhabitedHere : Bool
    actualActionRecognitionInhabitedHereIsFalse :
      actualActionRecognitionInhabitedHere ≡ false

canonicalActualActionRecognitionBoundary : ActualActionRecognitionBoundary
canonicalActualActionRecognitionBoundary =
  actual-action-recognition-boundary
    true refl
    true refl
    true refl
    true refl
    false refl
