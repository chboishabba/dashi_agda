module DASHI.Physics.Closure.ClaySprintSeventySevenYMLargeFieldCutSeparationExactLemmaReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YMLargeFieldTemporalCutSeparation
  as W3

------------------------------------------------------------------------
-- Sprint 77 YM large-field cut separation exact lemma receipt.
--
-- This receipt refines the W3 authority boundary into an exact lemma
-- contract.  The local W3 range inputs are present, but the requested
-- theorem LargeFieldPolymersDoNotCrossTransferCut remains false/open until
-- the four named analytic lemmas are provided as real proof objects.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data Sprint77YMExactMissingLemma : Set where
  CutAdaptedLargeFieldPolymerGeometry :
    Sprint77YMExactMissingLemma
  UniformLargeFieldSuppressionAtTransferCut :
    Sprint77YMExactMissingLemma
  SlowFieldSmallFieldInterfaceCompatibility :
    Sprint77YMExactMissingLemma
  LargeFieldClusterExpansionRespectsTemporalSlabs :
    Sprint77YMExactMissingLemma

canonicalSprint77YMExactMissingLemmas :
  List Sprint77YMExactMissingLemma
canonicalSprint77YMExactMissingLemmas =
  CutAdaptedLargeFieldPolymerGeometry
  ∷ UniformLargeFieldSuppressionAtTransferCut
  ∷ SlowFieldSmallFieldInterfaceCompatibility
  ∷ LargeFieldClusterExpansionRespectsTemporalSlabs
  ∷ []

data Sprint77YMW3LocalRangeInput : Set where
  KernelRangeRKEqualsOne :
    Sprint77YMW3LocalRangeInput
  BlockingScaleLEqualsTwo :
    Sprint77YMW3LocalRangeInput
  KernelRangeStrictlyBelowBlockingScale :
    Sprint77YMW3LocalRangeInput

canonicalSprint77YMW3LocalRangeInputs :
  List Sprint77YMW3LocalRangeInput
canonicalSprint77YMW3LocalRangeInputs =
  KernelRangeRKEqualsOne
  ∷ BlockingScaleLEqualsTwo
  ∷ KernelRangeStrictlyBelowBlockingScale
  ∷ []

data Sprint77YMOpenTarget : Set where
  LargeFieldPolymersDoNotCrossTransferCut :
    Sprint77YMOpenTarget

data Sprint77YMPromotion : Set where

sprint77YMPromotionImpossibleHere :
  Sprint77YMPromotion →
  ⊥
sprint77YMPromotionImpossibleHere ()

sprint77YMExactLemmaContractStatement : String
sprint77YMExactLemmaContractStatement =
  "Sprint 77 exact lemma contract: W3 supplies local range inputs r_K=1, L=2, and r_K<L, but LargeFieldPolymersDoNotCrossTransferCut is still false/open. Closing it requires CutAdaptedLargeFieldPolymerGeometry, UniformLargeFieldSuppressionAtTransferCut, SlowFieldSmallFieldInterfaceCompatibility, and LargeFieldClusterExpansionRespectsTemporalSlabs."

sprint77YMBoundary : String
sprint77YMBoundary =
  "Boundary: this receipt names the exact missing W3 large-field temporal cut separation lemmas only. It adds no postulates, proves no promotion, and keeps clayYangMillsPromoted=false."

record ClaySprintSeventySevenYMLargeFieldCutSeparationExactLemmaReceipt :
  Set₁ where
  field
    w3NoPromotion :
      W3.clayYangMillsPromoted ≡ false

    w3ClosedInputsAreCanonical :
      W3.YMLargeFieldTemporalCutSeparationReceipt.closedInputs
        W3.canonicalYMLargeFieldTemporalCutSeparationReceipt
        ≡ W3.canonicalW3ClosedInputs

    w3KernelRange :
      String
    w3KernelRangeIsRKOne :
      w3KernelRange ≡ "r_K = 1"
    w3KernelRangeMatchesW3 :
      w3KernelRange
        ≡ W3.YMLargeFieldTemporalCutSeparationReceipt.kernelRange
          W3.canonicalYMLargeFieldTemporalCutSeparationReceipt

    w3BlockingScale :
      String
    w3BlockingScaleIsLTwo :
      w3BlockingScale ≡ "L = 2"
    w3BlockingScaleMatchesW3 :
      w3BlockingScale
        ≡ W3.YMLargeFieldTemporalCutSeparationReceipt.blockingScale
          W3.canonicalYMLargeFieldTemporalCutSeparationReceipt

    w3RKLessThanL :
      Bool
    w3RKLessThanLIsTrue :
      w3RKLessThanL ≡ true
    w3RKLessThanLMatchesW3 :
      w3RKLessThanL
        ≡ W3.YMLargeFieldTemporalCutSeparationReceipt.rkLessThanL
          W3.canonicalYMLargeFieldTemporalCutSeparationReceipt

    w3LocalRangeInputs :
      List Sprint77YMW3LocalRangeInput
    w3LocalRangeInputsAreCanonical :
      w3LocalRangeInputs ≡ canonicalSprint77YMW3LocalRangeInputs

    openTarget :
      Sprint77YMOpenTarget
    openTargetIsLargeFieldPolymersDoNotCrossTransferCut :
      openTarget ≡ LargeFieldPolymersDoNotCrossTransferCut

    w3LargeFieldPolymersDoNotCrossTransferCut :
      Bool
    w3LargeFieldPolymersDoNotCrossTransferCutIsFalse :
      w3LargeFieldPolymersDoNotCrossTransferCut ≡ false
    w3LargeFieldPolymersDoNotCrossTransferCutMatchesW3 :
      w3LargeFieldPolymersDoNotCrossTransferCut
        ≡ W3.YMLargeFieldTemporalCutSeparationReceipt.largeFieldPolymersDoNotCrossTransferCut
          W3.canonicalYMLargeFieldTemporalCutSeparationReceipt

    cutAdaptedLargeFieldPolymerGeometry :
      Bool
    cutAdaptedLargeFieldPolymerGeometryIsFalse :
      cutAdaptedLargeFieldPolymerGeometry ≡ false

    uniformLargeFieldSuppressionAtTransferCut :
      Bool
    uniformLargeFieldSuppressionAtTransferCutIsFalse :
      uniformLargeFieldSuppressionAtTransferCut ≡ false

    slowFieldSmallFieldInterfaceCompatibility :
      Bool
    slowFieldSmallFieldInterfaceCompatibilityIsFalse :
      slowFieldSmallFieldInterfaceCompatibility ≡ false

    largeFieldClusterExpansionRespectsTemporalSlabs :
      Bool
    largeFieldClusterExpansionRespectsTemporalSlabsIsFalse :
      largeFieldClusterExpansionRespectsTemporalSlabs ≡ false

    exactMissingLemmas :
      List Sprint77YMExactMissingLemma
    exactMissingLemmasAreCanonical :
      exactMissingLemmas ≡ canonicalSprint77YMExactMissingLemmas

    exactLemmaContractStatement :
      String
    exactLemmaContractStatementIsCanonical :
      exactLemmaContractStatement ≡ sprint77YMExactLemmaContractStatement

    boundary :
      String
    boundaryIsCanonical :
      boundary ≡ sprint77YMBoundary

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    promotions :
      List Sprint77YMPromotion
    promotionsAreEmpty :
      promotions ≡ []
    noPromotionPossibleHere :
      Sprint77YMPromotion → ⊥

canonicalSprint77YMLargeFieldCutSeparationExactLemmaReceipt :
  ClaySprintSeventySevenYMLargeFieldCutSeparationExactLemmaReceipt
canonicalSprint77YMLargeFieldCutSeparationExactLemmaReceipt =
  record
    { w3NoPromotion = refl
    ; w3ClosedInputsAreCanonical = refl
    ; w3KernelRange = "r_K = 1"
    ; w3KernelRangeIsRKOne = refl
    ; w3KernelRangeMatchesW3 = refl
    ; w3BlockingScale = "L = 2"
    ; w3BlockingScaleIsLTwo = refl
    ; w3BlockingScaleMatchesW3 = refl
    ; w3RKLessThanL = true
    ; w3RKLessThanLIsTrue = refl
    ; w3RKLessThanLMatchesW3 = refl
    ; w3LocalRangeInputs = canonicalSprint77YMW3LocalRangeInputs
    ; w3LocalRangeInputsAreCanonical = refl
    ; openTarget = LargeFieldPolymersDoNotCrossTransferCut
    ; openTargetIsLargeFieldPolymersDoNotCrossTransferCut = refl
    ; w3LargeFieldPolymersDoNotCrossTransferCut = false
    ; w3LargeFieldPolymersDoNotCrossTransferCutIsFalse = refl
    ; w3LargeFieldPolymersDoNotCrossTransferCutMatchesW3 = refl
    ; cutAdaptedLargeFieldPolymerGeometry = false
    ; cutAdaptedLargeFieldPolymerGeometryIsFalse = refl
    ; uniformLargeFieldSuppressionAtTransferCut = false
    ; uniformLargeFieldSuppressionAtTransferCutIsFalse = refl
    ; slowFieldSmallFieldInterfaceCompatibility = false
    ; slowFieldSmallFieldInterfaceCompatibilityIsFalse = refl
    ; largeFieldClusterExpansionRespectsTemporalSlabs = false
    ; largeFieldClusterExpansionRespectsTemporalSlabsIsFalse = refl
    ; exactMissingLemmas = canonicalSprint77YMExactMissingLemmas
    ; exactMissingLemmasAreCanonical = refl
    ; exactLemmaContractStatement = sprint77YMExactLemmaContractStatement
    ; exactLemmaContractStatementIsCanonical = refl
    ; boundary = sprint77YMBoundary
    ; boundaryIsCanonical = refl
    ; clayYangMillsPromotedIsFalse = refl
    ; promotions = []
    ; promotionsAreEmpty = refl
    ; noPromotionPossibleHere = sprint77YMPromotionImpossibleHere
    }
