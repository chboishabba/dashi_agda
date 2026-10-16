module DASHI.Biology.IITCubeExceptionalGeometryHandoffExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Biology.IITCubeTwoFaceQ9SelfIndexingWeldExact as Weld
import DASHI.Biology.IITCubeTwoFaceImageRecognitionExact as Image

------------------------------------------------------------------------
-- HANDOFF TO LILA / E6 / E8 / FIRST-TITS
--
-- The selected ternary cube has the same sector/row/column index shape as the
-- sibling first-Tits M3^3 basis, but matching index shape is not same-object
-- authority.  The cube programme now has an exact two-face graph target and a
-- proof-relevant concrete-image recognition interface.  The exceptional and
-- LILA programmes therefore receive precise preservation/intertwiner payments.
------------------------------------------------------------------------

record SiblingExceptionalSourceReceipt : Set where
  constructor sibling-exceptional-source-receipt
  field
    firstTitsPR : Nat
    firstTitsObservedHead : String
    firstTitsUsesLiteralSectorRowColumn27Basis : Bool
    firstTitsOwnsLiteralSL3CubedSameCarrierAction : Bool
    firstTitsRecoversE6RootsFromThatAction : Bool
    lilaPR : Nat
    lilaObservedHead : String
    lilaSeparatesGeometryLocalLawTopologyConsumer : Bool
    unmergedSiblingTheoremAuthorityImported : Bool

canonicalSiblingExceptionalSourceReceipt : SiblingExceptionalSourceReceipt
canonicalSiblingExceptionalSourceReceipt =
  sibling-exceptional-source-receipt
    1106
    "11ef40286b2f00e351d4558806b018392f728d46"
    true true true
    1095
    "a0eb2965dcf3b6891622a5b1c58ede72bafcbd06"
    true
    false

------------------------------------------------------------------------
-- 1. Exact action-preservation payment for an image/kernel decomposition.
------------------------------------------------------------------------

record ActionPreservesImageKernel
    (Group Carrier : Set)
    (act : Group → Carrier → Carrier)
    (ImagePart KernelPart : Carrier → Set) : Set₁ where
  field
    preservesImage :
      (g : Group) (x : Carrier) →
      ImagePart x → ImagePart (act g x)
    preservesKernel :
      (g : Group) (x : Carrier) →
      KernelPart x → KernelPart (act g x)

open ActionPreservesImageKernel public

------------------------------------------------------------------------
-- 2. Exact hidden-state / cube-dynamics intertwiner payment for LILA/LLM.
------------------------------------------------------------------------

record HiddenCubeIntertwiner
    (Hidden Cube : Set)
    (hiddenStep : Hidden → Hidden)
    (cubeStep : Cube → Cube) : Set₁ where
  field
    project : Hidden → Cube
    intertwinesStep :
      (hidden : Hidden) →
      project (hiddenStep hidden) ≡ cubeStep (project hidden)

open HiddenCubeIntertwiner public

------------------------------------------------------------------------
-- 3. Held-out consumer payment remains separate from representation fit.
------------------------------------------------------------------------

record HiddenCubeConsumerPayment
    (Hidden Cube Consumer : Set)
    (projection : Hidden → Cube)
    (hiddenConsumer : Hidden → Consumer)
    (cubeConsumer : Cube → Consumer) : Set₁ where
  field
    consumerFactorsThroughProjection :
      (hidden : Hidden) →
      cubeConsumer (projection hidden) ≡ hiddenConsumer hidden

------------------------------------------------------------------------
-- 4. Current boundary.
------------------------------------------------------------------------

record ExceptionalCubeHandoffBoundary : Set where
  field
    ternaryCubeHasThreeNineSiteFaceCoordinates : Bool
    numericalCubeImageHasEighteenCoordinates : Bool
    numericalCubeKernelHasNineCoordinates : Bool
    twoFaceTargetIsQ9Field9 : Bool
    algebraicTwoFaceGraphCompilerSourceWritten : Bool

    matchingNinePlusNinePlusNineDimensionsProvesSameObject : Bool
    concreteTorusImageRecognitionKernelPaid : Bool
    e6ActionPreservesCubeImageKernelSplitByDefinition : Bool
    e8RootCodebookPreservesCubeImageKernelSplitByDefinition : Bool
    lilaHiddenStateProjectionIsCubeIntertwinerByDefinition : Bool

    sameObjectActionIntertwinerStillRequired : Bool
    heldOutFutureConsumerTestStillRequired : Bool

canonicalExceptionalCubeHandoffBoundary : ExceptionalCubeHandoffBoundary
canonicalExceptionalCubeHandoffBoundary = record
  { ternaryCubeHasThreeNineSiteFaceCoordinates = true
  ; numericalCubeImageHasEighteenCoordinates = true
  ; numericalCubeKernelHasNineCoordinates = true
  ; twoFaceTargetIsQ9Field9 = true
  ; algebraicTwoFaceGraphCompilerSourceWritten = true
  ; matchingNinePlusNinePlusNineDimensionsProvesSameObject = false
  ; concreteTorusImageRecognitionKernelPaid = false
  ; e6ActionPreservesCubeImageKernelSplitByDefinition = false
  ; e8RootCodebookPreservesCubeImageKernelSplitByDefinition = false
  ; lilaHiddenStateProjectionIsCubeIntertwinerByDefinition = false
  ; sameObjectActionIntertwinerStillRequired = true
  ; heldOutFutureConsumerTestStillRequired = true
  }

sameDimensionsDoNotPromote :
  matchingNinePlusNinePlusNineDimensionsProvesSameObject
    canonicalExceptionalCubeHandoffBoundary ≡ false
sameDimensionsDoNotPromote = refl

intertwinerStillRequired :
  sameObjectActionIntertwinerStillRequired
    canonicalExceptionalCubeHandoffBoundary ≡ true
intertwinerStillRequired = refl

q9TargetBoundary : Weld.CubeQ9WeldBoundary
q9TargetBoundary = Weld.canonicalCubeQ9WeldBoundary

cubeGraphBoundary : Image.CubeImageRecognitionBoundary
cubeGraphBoundary = Image.canonicalCubeImageRecognitionBoundary
