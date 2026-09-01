module DASHI.Moonshine.Base369Monster3BActualSectorRecognitionBidiExact where

------------------------------------------------------------------------
-- ACTUAL MN3B ZETA-SECTOR RECOGNITION -> BASE369 RECOGNITION
--
-- The repository already owns the exact appraisal-fibre <-> X6 chart and the
-- actual-sector recognition interface
--
--   ActualSector <-> X6 x Fin 90
--
-- with translation and modulation-exponent intertwining.  This module merely
-- composes those already-owned interfaces.  It does not infer recognition from
-- dimension or character equality.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (Fin)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import DASHI.Algebra.Trit using (Trit)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteProjectorModelExact as Model
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Actual
import DASHI.Moonshine.Base369AppraisalFibreHeisenbergCarrierBidiExact as Fibre

------------------------------------------------------------------------
-- 1. Base369 multiplicity carrier.
------------------------------------------------------------------------

Base369MultiplicityBasis : Set
Base369MultiplicityBasis = Geometry.AppraisalFibrePoint × Fin 90

base369ToModel : Base369MultiplicityBasis → Model.ZetaModelBasis
base369ToModel (fibre , multiplicity) =
  Model.zetaBasis (Fibre.appraisalFibreToX6 fibre) multiplicity

modelToBase369 : Model.ZetaModelBasis → Base369MultiplicityBasis
modelToBase369 basis =
  Fibre.x6ToAppraisalFibre (Model.weightPosition basis) ,
  Model.multiplicityCoordinate basis

base369ModelRoundTrip :
  (basis : Base369MultiplicityBasis) →
  modelToBase369 (base369ToModel basis) ≡ basis
base369ModelRoundTrip (fibre , multiplicity)
  rewrite Fibre.appraisalFibreRoundTrip fibre = refl

modelBase369RoundTrip :
  (basis : Model.ZetaModelBasis) →
  base369ToModel (modelToBase369 basis) ≡ basis
modelBase369RoundTrip (Model.zetaBasis position multiplicity)
  rewrite Fibre.x6RoundTrip position = refl

------------------------------------------------------------------------
-- 2. Compose an actual-sector recognition with the exact Base369 chart.
------------------------------------------------------------------------

record ActualBase369SectorRecognition (ActualSector : Set) : Set where
  constructor actual-base369-sector-recognition
  field
    sourceRecognition : Actual.ActualZetaSectorRecognition ActualSector
    toBase369 : ActualSector → Base369MultiplicityBasis
    fromBase369 : Base369MultiplicityBasis → ActualSector
    fromAfterTo : (state : ActualSector) → fromBase369 (toBase369 state) ≡ state
    toAfterFrom :
      (basis : Base369MultiplicityBasis) → toBase369 (fromBase369 basis) ≡ basis
open ActualBase369SectorRecognition public

composeActualRecognitionWithBase369 :
  ∀ {ActualSector} →
  Actual.ActualZetaSectorRecognition ActualSector →
  ActualBase369SectorRecognition ActualSector
composeActualRecognitionWithBase369 recognition =
  actual-base369-sector-recognition
    recognition
    (λ state → modelToBase369 (Actual.toModel recognition state))
    (λ basis → Actual.fromModel recognition (base369ToModel basis))
    (λ state →
      trans
        (cong (Actual.fromModel recognition)
          (modelBase369RoundTrip (Actual.toModel recognition state)))
        (Actual.fromAfterTo recognition state))
    (λ basis →
      trans
        (cong modelToBase369
          (Actual.toAfterFrom recognition (base369ToModel basis)))
        (base369ModelRoundTrip basis))

------------------------------------------------------------------------
-- 3. The six Heisenberg translations become literal Base369 fibre transport.
------------------------------------------------------------------------

base369Translate :
  H.Axis6 → Geometry.AppraisalFibrePoint → Geometry.AppraisalFibrePoint
base369Translate axis fibre =
  Fibre.x6ToAppraisalFibre
    (H.translate axis (Fibre.appraisalFibreToX6 fibre))

base369TranslateChartsToHeisenberg :
  (axis : H.Axis6) → (fibre : Geometry.AppraisalFibrePoint) →
  Fibre.appraisalFibreToX6 (base369Translate axis fibre)
  ≡ H.translate axis (Fibre.appraisalFibreToX6 fibre)
base369TranslateChartsToHeisenberg axis fibre =
  Fibre.x6RoundTrip (H.translate axis (Fibre.appraisalFibreToX6 fibre))

translateBase369Multiplicity :
  H.Axis6 → Base369MultiplicityBasis → Base369MultiplicityBasis
translateBase369Multiplicity axis (fibre , multiplicity) =
  base369Translate axis fibre , multiplicity

actualTranslationIntertwinesBase369 :
  ∀ {ActualSector}
    (recognition : Actual.ActualZetaSectorRecognition ActualSector) →
    (axis : H.Axis6) → (state : ActualSector) →
  toBase369 (composeActualRecognitionWithBase369 recognition)
    (Actual.actualTranslate recognition axis state)
  ≡ translateBase369Multiplicity axis
      (toBase369 (composeActualRecognitionWithBase369 recognition) state)
actualTranslationIntertwinesBase369 recognition axis state
  rewrite Actual.translationIntertwines recognition axis state =
  let basis = Actual.toModel recognition state
  in
  caseBasis basis
  where
  caseBasis :
    (basis : Model.ZetaModelBasis) →
    modelToBase369 (Model.translatedBasis axis basis)
    ≡ translateBase369Multiplicity axis (modelToBase369 basis)
  caseBasis (Model.zetaBasis position multiplicity)
    rewrite Fibre.x6RoundTrip (H.translate axis position) = refl

------------------------------------------------------------------------
-- 4. Modulation observers transport too; no phase semantics are invented.
------------------------------------------------------------------------

base369ModulationExponent : H.Axis6 → Geometry.AppraisalFibrePoint → Trit
base369ModulationExponent axis fibre =
  H.modulationExponent axis (Fibre.appraisalFibreToX6 fibre)

actualModulationExponentIntertwinesBase369 :
  ∀ {ActualSector}
    (recognition : Actual.ActualZetaSectorRecognition ActualSector) →
    (axis : H.Axis6) → (state : ActualSector) →
  Actual.actualModulationExponent recognition axis state
  ≡ base369ModulationExponent axis
      (proj₁ (toBase369 (composeActualRecognitionWithBase369 recognition) state))
actualModulationExponentIntertwinesBase369 recognition axis state =
  trans
    (Actual.modulationExponentIntertwines recognition axis state)
    refl

------------------------------------------------------------------------
-- 5. Boundary.
------------------------------------------------------------------------

record ActualBase369RecognitionBoundary : Set where
  constructor actual-base369-recognition-boundary
  field
    exactBase369ModelRoundTripConstructed : Bool
    actualRecognitionComposesToBase369 : Bool
    translationIntertwiningTransported : Bool
    modulationObserverIntertwiningTransported : Bool
    characterEqualityAloneUsedAsRecognition : Bool
    dimensionEqualityAloneUsedAsRecognition : Bool
open ActualBase369RecognitionBoundary public

canonicalActualBase369RecognitionBoundary : ActualBase369RecognitionBoundary
canonicalActualBase369RecognitionBoundary =
  actual-base369-recognition-boundary true true true true false false
