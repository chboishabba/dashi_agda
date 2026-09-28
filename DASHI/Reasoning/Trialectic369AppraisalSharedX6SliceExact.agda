module DASHI.Reasoning.Trialectic369AppraisalSharedX6SliceExact where

------------------------------------------------------------------------
-- TRIALECTIC CECH SAME-OBJECT PROMOTION THROUGH THE APPRAISAL FIBRE
--
-- DASHI CONTRIBUTION
--
-- The Base369 appraisal fibre is already exactly charted by the finite
-- Heisenberg X6 carrier:
--
--   AppraisalFibrePoint <-> X6.
--
-- The Heisenberg translation action has also already been transported through
-- that chart.  Therefore AppraisalFibrePoint supplies the literal shared
-- actual-state carrier required by the generic face-hypercube gluing compiler.
--
-- This closes the model-level same-object promotion for the selected trialectic
-- corner star.  It does NOT:
--
--   * identify the relational Grothendieck site with the full X6 boundary nerve;
--   * identify the appraisal fibre with an external Monster representation;
--   * identify cyclic Heisenberg translation with native non-periodic P3 path
--     adjacency.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Base369AppraisalFibreHeisenbergCarrierBidiExact as Carrier
import DASHI.Moonshine.Base369HeisenbergTranslationGridObstructionExact as Translation
import DASHI.Moonshine.Base369Ternary27FaceHypercubeCechGluingBidiExact as Cech
import DASHI.Reasoning.ActualFaceHypercubeGluingFromSharedSliceExact as Shared
import DASHI.Reasoning.Trialectic369CechCornerStarRecognitionExact as Corner

------------------------------------------------------------------------
-- 1. One literal X6 slice inside the appraisal fibre.
------------------------------------------------------------------------

appraisalInclude :
  H.X6 ->
  Geometry.AppraisalFibrePoint
appraisalInclude =
  Carrier.x6ToAppraisalFibre

appraisalIncludeInjective :
  {left right : H.X6} ->
  appraisalInclude left ≡ appraisalInclude right ->
  left ≡ right
appraisalIncludeInjective {left} {right} equality =
  trans
    (sym (Carrier.x6RoundTrip left))
    (trans
      (cong Carrier.appraisalFibreToX6 equality)
      (Carrier.x6RoundTrip right))

------------------------------------------------------------------------
-- 2. Existing transported Heisenberg action intertwines the slice exactly.
------------------------------------------------------------------------

appraisalIncludeIntertwines :
  (axis : H.Axis6) ->
  (state : H.X6) ->
  appraisalInclude (H.translate axis state)
  ≡
  Translation.heisenbergTranslateFibre axis
    (appraisalInclude state)
appraisalIncludeIntertwines axis state =
  cong
    (λ x -> Carrier.x6ToAppraisalFibre (H.translate axis x))
    (sym (Carrier.x6RoundTrip state))

------------------------------------------------------------------------
-- 3. Package the generic shared-slice recognition.
------------------------------------------------------------------------

appraisalSharedSliceRecognition :
  Shared.SharedActualX6SliceRecognition
    H.Axis6
    Geometry.AppraisalFibrePoint
appraisalSharedSliceRecognition = record
  { modelAct = H.translate
  ; actualAct = Translation.heisenbergTranslateFibre
  ; include = appraisalInclude
  ; includeInjective = appraisalIncludeInjective
  ; includeIntertwines = appraisalIncludeIntertwines
  }

------------------------------------------------------------------------
-- 4. Compile the selected trialectic corner-star recognition.
------------------------------------------------------------------------

trialecticAppraisalSharedSliceRecognition :
  Corner.CornerStarSharedSliceRecognition
    H.Axis6
    Geometry.AppraisalFibrePoint
trialecticAppraisalSharedSliceRecognition =
  Corner.corner-star-shared-slice-recognition
    appraisalSharedSliceRecognition
    refl
    refl
    refl

trialecticAppraisalActualStateRecognition :
  Corner.CornerStarActualStateRecognition
    H.Axis6
    Geometry.AppraisalFibrePoint
trialecticAppraisalActualStateRecognition =
  Corner.compileCornerStarActualStateRecognition
    trialecticAppraisalSharedSliceRecognition

------------------------------------------------------------------------
-- 5. Exact consequences.
------------------------------------------------------------------------

trialecticAppraisalFacePromotion :
  Cech.ActualFaceHypercubeGluingPromotion
    H.Axis6
    Geometry.AppraisalFibrePoint
trialecticAppraisalFacePromotion =
  Corner.actualPromotion trialecticAppraisalActualStateRecognition

data TrialecticAppraisalPromotionCreatesFullNerveEquivalence : Set where
data TrialecticAppraisalPromotionCreatesMonsterRepresentation : Set where
data CyclicTranslationBecomesNativePathAdjacency : Set where

appraisalPromotionDoesNotCreateFullNerveEquivalence :
  TrialecticAppraisalPromotionCreatesFullNerveEquivalence -> ⊥
appraisalPromotionDoesNotCreateFullNerveEquivalence ()

appraisalPromotionDoesNotCreateMonsterRepresentation :
  TrialecticAppraisalPromotionCreatesMonsterRepresentation -> ⊥
appraisalPromotionDoesNotCreateMonsterRepresentation ()

cyclicTranslationStillNotNativePathAdjacency :
  CyclicTranslationBecomesNativePathAdjacency -> ⊥
cyclicTranslationStillNotNativePathAdjacency ()

record Trialectic369AppraisalSharedX6SliceBoundary : Set where
  constructor trialectic-369-appraisal-shared-x6-slice-boundary
  field
    appraisalFibreX6BijectionReused : Bool
    sharedActualX6SliceConstructed : Bool
    sharedSliceInclusionInjective : Bool
    heisenbergActionIntertwinedExactly : Bool
    fullSixFacePromotionCompiled : Bool
    selectedCornerStarSameObjectPromotionPaid : Bool
    fullNerveEquivalencePaid : Bool
    monsterRepresentationRecognized : Bool
    cyclicTranslationEqualsNativePathAdjacency : Bool

canonicalTrialectic369AppraisalSharedX6SliceBoundary :
  Trialectic369AppraisalSharedX6SliceBoundary
canonicalTrialectic369AppraisalSharedX6SliceBoundary =
  trialectic-369-appraisal-shared-x6-slice-boundary
    true true true true true true
    false false false
