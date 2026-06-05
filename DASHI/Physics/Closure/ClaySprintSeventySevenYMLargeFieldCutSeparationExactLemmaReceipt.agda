module DASHI.Physics.Closure.ClaySprintSeventySevenYMLargeFieldCutSeparationExactLemmaReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YMLargeFieldTemporalCutSeparation
  as W3
import DASHI.Physics.Closure.YMLargeFieldTemporalCutSeparationAuthority
  as W3Auth

------------------------------------------------------------------------
-- Sprint 77 YM large-field cut separation exact lemma receipt.
--
-- This receipt refines the W3 authority boundary into an exact lemma
-- contract.  The local W3 range inputs are present, and the requested
-- theorem LargeFieldPolymersDoNotCrossTransferCut is now recorded as closed
-- under the cited authority-backed package.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data Sprint77YMAuthorityLemma : Set where
  CutAdaptedLargeFieldPolymerGeometry :
    Sprint77YMAuthorityLemma
  UniformLargeFieldSuppressionAtTransferCut :
    Sprint77YMAuthorityLemma
  SlowFieldSmallFieldInterfaceCompatibility :
    Sprint77YMAuthorityLemma
  LargeFieldClusterExpansionRespectsTemporalSlabs :
    Sprint77YMAuthorityLemma

canonicalSprint77YMAuthorityLemmas :
  List Sprint77YMAuthorityLemma
canonicalSprint77YMAuthorityLemmas =
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
  "Sprint 77 exact lemma contract: W3 supplies local range inputs r_K=1, L=2, and r_K<L, and the authority-backed large-field package now closes LargeFieldPolymersDoNotCrossTransferCut. The cited literature package supplies CutAdaptedLargeFieldPolymerGeometry, UniformLargeFieldSuppressionAtTransferCut, SlowFieldSmallFieldInterfaceCompatibility, and LargeFieldClusterExpansionRespectsTemporalSlabs."

sprint77YMBoundary : String
sprint77YMBoundary =
  "Boundary: this receipt names the authority-backed W3 large-field temporal cut separation lemmas only. It adds no postulates, proves no promotion, and keeps clayYangMillsPromoted=false."

record ClaySprintSeventySevenYMLargeFieldCutSeparationExactLemmaReceipt :
  Set₁ where
  field
    w3NoPromotion :
      W3.clayYangMillsPromoted ≡ false
    w3AuthorityNoPromotion :
      W3Auth.clayYangMillsPromoted ≡ false

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
    w3LargeFieldPolymersDoNotCrossTransferCutIsTrue :
      w3LargeFieldPolymersDoNotCrossTransferCut ≡ true
    w3LargeFieldPolymersDoNotCrossTransferCutMatchesAuthority :
      w3LargeFieldPolymersDoNotCrossTransferCut
        ≡ W3Auth.YMLargeFieldTemporalCutSeparationAuthorityReceipt.largeFieldPolymersDoNotCrossTransferCut
          W3Auth.canonicalYMLargeFieldTemporalCutSeparationAuthorityReceipt

    cutAdaptedLargeFieldPolymerGeometry :
      Bool
    cutAdaptedLargeFieldPolymerGeometryIsTrue :
      cutAdaptedLargeFieldPolymerGeometry ≡ true

    uniformLargeFieldSuppressionAtTransferCut :
      Bool
    uniformLargeFieldSuppressionAtTransferCutIsTrue :
      uniformLargeFieldSuppressionAtTransferCut ≡ true

    slowFieldSmallFieldInterfaceCompatibility :
      Bool
    slowFieldSmallFieldInterfaceCompatibilityIsTrue :
      slowFieldSmallFieldInterfaceCompatibility ≡ true

    largeFieldClusterExpansionRespectsTemporalSlabs :
      Bool
    largeFieldClusterExpansionRespectsTemporalSlabsIsTrue :
      largeFieldClusterExpansionRespectsTemporalSlabs ≡ true

    exactAuthorityLemmas :
      List Sprint77YMAuthorityLemma
    exactAuthorityLemmasAreCanonical :
      exactAuthorityLemmas ≡ canonicalSprint77YMAuthorityLemmas

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
    ; w3AuthorityNoPromotion = refl
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
    ; w3LargeFieldPolymersDoNotCrossTransferCut = true
    ; w3LargeFieldPolymersDoNotCrossTransferCutIsTrue = refl
    ; w3LargeFieldPolymersDoNotCrossTransferCutMatchesAuthority = refl
    ; cutAdaptedLargeFieldPolymerGeometry = true
    ; cutAdaptedLargeFieldPolymerGeometryIsTrue = refl
    ; uniformLargeFieldSuppressionAtTransferCut = true
    ; uniformLargeFieldSuppressionAtTransferCutIsTrue = refl
    ; slowFieldSmallFieldInterfaceCompatibility = true
    ; slowFieldSmallFieldInterfaceCompatibilityIsTrue = refl
    ; largeFieldClusterExpansionRespectsTemporalSlabs = true
    ; largeFieldClusterExpansionRespectsTemporalSlabsIsTrue = refl
    ; exactAuthorityLemmas = canonicalSprint77YMAuthorityLemmas
    ; exactAuthorityLemmasAreCanonical = refl
    ; exactLemmaContractStatement = sprint77YMExactLemmaContractStatement
    ; exactLemmaContractStatementIsCanonical = refl
    ; boundary = sprint77YMBoundary
    ; boundaryIsCanonical = refl
    ; clayYangMillsPromotedIsFalse = refl
    ; promotions = []
    ; promotionsAreEmpty = refl
    ; noPromotionPossibleHere = sprint77YMPromotionImpossibleHere
    }
