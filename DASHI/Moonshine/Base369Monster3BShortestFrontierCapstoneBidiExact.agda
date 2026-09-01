module DASHI.Moonshine.Base369Monster3BShortestFrontierCapstoneBidiExact where

------------------------------------------------------------------------
-- SHORTEST BIDI FRONTIER CAPSTONE
--
-- This owner composes the current same-object Monster/VOA/CTblLib lane:
--
--   literal selected g3
--     -> certified central-zeta kernel class / Monster-3B fusion receipt
--     -> literal VOA zeta eigenspace
--     -> ActualZetaSectorRecognition
--     -> X6 x Fin 90
--     -> all 90 actual Base369 appraisal 729-slices.
--
-- The point is compression of scientific inputs.  Everything after the two
-- genuinely external receipts
--
--   (1) selected literal element represents the certified central-3B class;
--   (2) the literal zeta eigenspace is action-recognized as X6 x Fin 90
--
-- is compiler output.  No cardinality-only promotion is introduced.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Fin.Base using (Fin)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Recognition
import DASHI.Moonshine.MonsterGradedVOAActual3BKernelSameElementBidiExact as KernelWeld
import DASHI.Moonshine.Base369Monster3BActualMultiplicitySliceAppraisalBidiExact as Slice

------------------------------------------------------------------------
-- 1. One capstone source: same-element CTblLib attachment + recognition of
--    the literal zeta sector generated from that exact selected element.
------------------------------------------------------------------------

record Shortest3BFrontierSource (Monster K : Set) : Setω where
  field
    attachment : KernelWeld.Actual3BKernelSameElementAttachment Monster K
    recognition :
      Recognition.ActualZetaSectorRecognition
        (KernelWeld.selectedLiteralZetaSector attachment)

open Shortest3BFrontierSource public

ActualZetaSector :
  ∀ {Monster K} → Shortest3BFrontierSource Monster K → Set
ActualZetaSector source =
  KernelWeld.selectedLiteralZetaSector (attachment source)

------------------------------------------------------------------------
-- 2. Character-theoretic consequences of the same selected element.
------------------------------------------------------------------------

selectedCentralZetaAmplitudeIs65610 :
  ∀ {Monster K}
    (source : Shortest3BFrontierSource Monster K) →
  DASHI.Moonshine.Monster3BKernelCharacterCriterionExact.coefficientZeta
    (KernelWeld.selectedActualRestrictedCharacter (attachment source))
  ≡ 65610
selectedCentralZetaAmplitudeIs65610 source =
  KernelWeld.selectedCentralZetaAmplitudeIs65610 (attachment source)

selectedKernelMultiplicityIsNinety :
  ∀ {Monster K}
    (source : Shortest3BFrontierSource Monster K) →
  DASHI.Moonshine.Monster3BActualKernelCharacterPromotionExact.multiplicity
    (KernelWeld.selectedKernelNinetyHeisenbergIsotypy (attachment source))
  ≡ 90
selectedKernelMultiplicityIsNinety source =
  KernelWeld.selectedKernelMultiplicityIsNinety (attachment source)

------------------------------------------------------------------------
-- 3. The literal recognition exports exact X6 and Fin 90 coordinates.
------------------------------------------------------------------------

actualWeight :
  ∀ {Monster K}
    (source : Shortest3BFrontierSource Monster K) →
  ActualZetaSector source → H.X6
actualWeight source = Recognition.actualWeightPosition (recognition source)

actualMultiplicity :
  ∀ {Monster K}
    (source : Shortest3BFrontierSource Monster K) →
  ActualZetaSector source → Fin 90
actualMultiplicity source =
  Recognition.actualMultiplicityCoordinate (recognition source)

------------------------------------------------------------------------
-- 4. All 90 actual 729 appraisal slices are compiler output.
------------------------------------------------------------------------

actualStateAtAppraisal :
  ∀ {Monster K}
    (source : Shortest3BFrontierSource Monster K) →
  Fin 90 → Geometry.AppraisalFibrePoint → ActualZetaSector source
actualStateAtAppraisal source =
  Slice.actualStateAtAppraisal (recognition source)

actualSliceWeight :
  ∀ {Monster K}
    (source : Shortest3BFrontierSource Monster K) →
  (m : Fin 90) →
  (point : Geometry.AppraisalFibrePoint) →
  actualWeight source (actualStateAtAppraisal source m point)
  ≡ DASHI.Moonshine.Base369AppraisalFibreHeisenbergCarrierBidiExact.appraisalFibreToX6 point
actualSliceWeight source =
  Slice.actualStateAtAppraisalWeight (recognition source)

actualSliceMultiplicity :
  ∀ {Monster K}
    (source : Shortest3BFrontierSource Monster K) →
  (m : Fin 90) →
  (point : Geometry.AppraisalFibrePoint) →
  actualMultiplicity source (actualStateAtAppraisal source m point) ≡ m
actualSliceMultiplicity source =
  Slice.actualStateAtAppraisalMultiplicity (recognition source)

actualSliceInjective :
  ∀ {Monster K}
    (source : Shortest3BFrontierSource Monster K) →
  (m : Fin 90) →
  {left right : Geometry.AppraisalFibrePoint} →
  actualStateAtAppraisal source m left
  ≡ actualStateAtAppraisal source m right →
  left ≡ right
actualSliceInjective source =
  Slice.actualStateAtAppraisalInjective (recognition source)

actualSliceTranslationIntertwines :
  ∀ {Monster K}
    (source : Shortest3BFrontierSource Monster K) →
  (m : Fin 90) →
  (axis : H.Axis6) →
  (point : Geometry.AppraisalFibrePoint) →
  Recognition.actualTranslate (recognition source) axis
    (actualStateAtAppraisal source m point)
  ≡ actualStateAtAppraisal source m
      (DASHI.Moonshine.Base369HeisenbergTranslationGridObstructionExact.heisenbergTranslateFibre
        axis point)
actualSliceTranslationIntertwines source =
  Slice.actualAppraisalTranslationIntertwines (recognition source)

actualSliceModulationIntertwines :
  ∀ {Monster K}
    (source : Shortest3BFrontierSource Monster K) →
  (m : Fin 90) →
  (axis : H.Axis6) →
  (point : Geometry.AppraisalFibrePoint) →
  Recognition.actualModulationExponent (recognition source) axis
    (actualStateAtAppraisal source m point)
  ≡ H.modulationExponent axis
      (DASHI.Moonshine.Base369AppraisalFibreHeisenbergCarrierBidiExact.appraisalFibreToX6 point)
actualSliceModulationIntertwines source =
  Slice.actualAppraisalModulationExponentIntertwines (recognition source)

------------------------------------------------------------------------
-- 5. Exhaustion of each selected multiplicity fibre.
------------------------------------------------------------------------

actualStateRecoveredInOwnSlice :
  ∀ {Monster K}
    (source : Shortest3BFrontierSource Monster K) →
  (state : ActualZetaSector source) →
  state ≡
    actualStateAtAppraisal source
      (actualMultiplicity source state)
      (DASHI.Moonshine.Base369AppraisalFibreHeisenbergCarrierBidiExact.x6ToAppraisalFibre
        (actualWeight source state))
actualStateRecoveredInOwnSlice source state =
  Slice.actualStateRecoveredFromAppraisal
    (recognition source)
    (actualMultiplicity source state)
    state
    DASHI.Moonshine.Base369Monster3BShortestFrontierCapstoneBidiExact.refl

------------------------------------------------------------------------
-- 6. Frontier accounting.  The entire 729/90 tail is generated after the two
--    external same-object/action receipts.  This file does not fabricate them.
------------------------------------------------------------------------

record Shortest3BFrontierBoundary : Set where
  constructor shortest3BFrontierBoundary
  field
    literalSelectedElementAndVOAActionSameObject : Bool
    elementToCertifiedCentralThreeBClassReceiptIsInput : Bool
    trace53IsAttachedToSameSelectedElement : Bool
    centralZetaAmplitude65610Generated : Bool
    ninetyCopyCharacterIsotypyGenerated : Bool
    literalZetaSectorGeneratedFromSelectedAction : Bool
    actualZetaRecognitionIsInput : Bool
    x6TimesFin90CoordinatesGenerated : Bool
    allNinetyAppraisalSlicesGenerated : Bool
    everySliceHas729AppraisalStatesByExactChart : Bool
    translationIntertwiningGeneratedForEverySlice : Bool
    modulationObserverIntertwiningGeneratedForEverySlice : Bool
    classFusionInferredFromTrace53Alone : Bool
    actionRecognitionInferredFromCharacterIsotypy : Bool
    fullMonsterActionOnWhole19683HyperfabricProvedHere : Bool

canonicalShortest3BFrontierBoundary : Shortest3BFrontierBoundary
canonicalShortest3BFrontierBoundary =
  shortest3BFrontierBoundary
    true true true true true true true true true true true true
    false false false
