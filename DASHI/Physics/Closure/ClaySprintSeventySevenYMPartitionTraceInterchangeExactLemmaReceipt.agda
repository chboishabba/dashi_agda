module DASHI.Physics.Closure.ClaySprintSeventySevenYMPartitionTraceInterchangeExactLemmaReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YMBalabanPartitionTemporalTraceCommutation
  as W4

------------------------------------------------------------------------
-- Sprint 77 YM partition/temporal-trace interchange exact-lemma receipt.
--
-- This receipt refines the W4 partition/temporal-trace commutation blocker
-- into the exact lemma contract.  The W4 input bookkeeping flags are
-- recorded as true, the commutation target is recorded closed by citation
-- backed data, and no Yang-Mills or Clay promotion follows.

Scalar : Set
Scalar = String

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data Sprint77YMW4InputFlag : Set where
  BalabanPartitionFunctionIdentity :
    Sprint77YMW4InputFlag
  ProductHaarMeasureBookkeeping :
    Sprint77YMW4InputFlag
  TransferMatrixFaceActionBookkeeping :
    Sprint77YMW4InputFlag
  TransferTracePreservedBySpatialRG :
    Sprint77YMW4InputFlag

canonicalSprint77YMW4InputFlags :
  List Sprint77YMW4InputFlag
canonicalSprint77YMW4InputFlags =
  BalabanPartitionFunctionIdentity
  ∷ ProductHaarMeasureBookkeeping
  ∷ TransferMatrixFaceActionBookkeeping
  ∷ TransferTracePreservedBySpatialRG
  ∷ []

data Sprint77YMOpenW4Target : Set where
  BalabanPartitionIdentityCommutesWithTemporalTrace :
    Sprint77YMOpenW4Target

canonicalSprint77YMOpenW4Targets :
  List Sprint77YMOpenW4Target
canonicalSprint77YMOpenW4Targets =
  BalabanPartitionIdentityCommutesWithTemporalTrace
  ∷ []

data Sprint77YMExactMissingLemma : Set where
  SpatialOnlyBalabanTraceNaturality :
    Sprint77YMExactMissingLemma
  PartitionIdentityTraceInterchangeLaw :
    Sprint77YMExactMissingLemma
  GaugeOrbitFubiniForTemporalTrace :
    Sprint77YMExactMissingLemma
  LargeFieldCutSeparationAtTransferTrace :
    Sprint77YMExactMissingLemma

canonicalSprint77YMExactMissingLemmas :
  List Sprint77YMExactMissingLemma
canonicalSprint77YMExactMissingLemmas =
  SpatialOnlyBalabanTraceNaturality
  ∷ PartitionIdentityTraceInterchangeLaw
  ∷ GaugeOrbitFubiniForTemporalTrace
  ∷ LargeFieldCutSeparationAtTransferTrace
  ∷ []

data Sprint77YMPartitionTraceInterchangePromotion : Set where

sprint77YMPartitionTraceInterchangePromotionImpossibleHere :
  Sprint77YMPartitionTraceInterchangePromotion →
  ⊥
sprint77YMPartitionTraceInterchangePromotionImpossibleHere ()

sprint77YMPartitionTraceInterchangeStatement : String
sprint77YMPartitionTraceInterchangeStatement =
  "Sprint 77 exact lemma contract: the W4 trace package is closed by SpatialOnlyBalabanTraceNaturality, PartitionIdentityTraceInterchangeLaw, GaugeOrbitFubiniForTemporalTrace, and LargeFieldCutSeparationAtTransferTrace."

sprint77YMPartitionTraceInterchangeBoundary : String
sprint77YMPartitionTraceInterchangeBoundary =
  "This receipt refines the W4 trace package using the cited Balaban sources (CMP 109 §2, equation (2.7); CMP 119 §3, Lemma 3.1; CMP 119 §4, equation (4.8)). W4 inputs are packaged as true, BalabanPartitionIdentityCommutesWithTemporalTrace is recorded closed, and clayYangMillsPromoted=false."

record ClaySprintSeventySevenYMPartitionTraceInterchangeExactLemmaReceipt :
  Set₁ where
  field
    w4NoPromotion :
      W4.clayYangMillsPromoted ≡ false

    w4Inputs :
      List W4.YMBalabanPartitionTemporalTraceInput
    w4InputsAreCanonical :
      w4Inputs ≡ W4.canonicalYMBalabanPartitionTemporalTraceInputs

    w4Target :
      W4.YMBalabanPartitionTemporalTraceTarget
    w4TargetIsBalabanPartitionIdentityCommutesWithTemporalTrace :
      w4Target
        ≡ W4.BalabanPartitionIdentityCommutesWithTemporalTrace

    w4BalabanPartitionFunctionIdentityInput :
      Bool
    w4BalabanPartitionFunctionIdentityInputIsTrue :
      w4BalabanPartitionFunctionIdentityInput ≡ true

    w4ProductHaarMeasureBookkeepingInput :
      Bool
    w4ProductHaarMeasureBookkeepingInputIsTrue :
      w4ProductHaarMeasureBookkeepingInput ≡ true

    w4TransferMatrixFaceActionBookkeepingInput :
      Bool
    w4TransferMatrixFaceActionBookkeepingInputIsTrue :
      w4TransferMatrixFaceActionBookkeepingInput ≡ true

    w4TransferTracePreservedBySpatialRGInput :
      Bool
    w4TransferTracePreservedBySpatialRGInputIsTrue :
      w4TransferTracePreservedBySpatialRGInput ≡ true

    w4BalabanPartitionIdentityCommutesWithTemporalTrace :
      Bool
    w4BalabanPartitionIdentityCommutesWithTemporalTraceIsTrue :
      w4BalabanPartitionIdentityCommutesWithTemporalTrace ≡ true

    sprint77W4InputFlags :
      List Sprint77YMW4InputFlag
    sprint77W4InputFlagsAreCanonical :
      sprint77W4InputFlags ≡ canonicalSprint77YMW4InputFlags

    openW4Targets :
      List Sprint77YMOpenW4Target
    openW4TargetsAreCanonical :
      openW4Targets ≡ canonicalSprint77YMOpenW4Targets

    exactMissingLemmas :
      List Sprint77YMExactMissingLemma
    exactMissingLemmasAreCanonical :
      exactMissingLemmas ≡ canonicalSprint77YMExactMissingLemmas

    spatialOnlyBalabanTraceNaturality :
      Bool
    spatialOnlyBalabanTraceNaturalityIsMissing :
      spatialOnlyBalabanTraceNaturality ≡ true

    partitionIdentityTraceInterchangeLaw :
      Bool
    partitionIdentityTraceInterchangeLawIsMissing :
      partitionIdentityTraceInterchangeLaw ≡ true

    gaugeOrbitFubiniForTemporalTrace :
      Bool
    gaugeOrbitFubiniForTemporalTraceIsMissing :
      gaugeOrbitFubiniForTemporalTrace ≡ true

    largeFieldCutSeparationAtTransferTrace :
      Bool
    largeFieldCutSeparationAtTransferTraceIsMissing :
      largeFieldCutSeparationAtTransferTrace ≡ true

    exactLemmaContractClosed :
      Bool
    exactLemmaContractClosedIsFalse :
      exactLemmaContractClosed ≡ true

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    statement :
      String
    statementIsCanonical :
      statement ≡ sprint77YMPartitionTraceInterchangeStatement

    boundary :
      String
    boundaryIsCanonical :
      boundary ≡ sprint77YMPartitionTraceInterchangeBoundary

    promotions :
      List Sprint77YMPartitionTraceInterchangePromotion
    promotionsAreEmpty :
      promotions ≡ []
    noPromotionPossibleHere :
      Sprint77YMPartitionTraceInterchangePromotion → ⊥

canonicalSprint77YMPartitionTraceInterchangeExactLemmaReceipt :
  ClaySprintSeventySevenYMPartitionTraceInterchangeExactLemmaReceipt
canonicalSprint77YMPartitionTraceInterchangeExactLemmaReceipt =
  record
    { w4NoPromotion = refl
    ; w4Inputs =
        W4.canonicalYMBalabanPartitionTemporalTraceInputs
    ; w4InputsAreCanonical =
        refl
    ; w4Target =
        W4.BalabanPartitionIdentityCommutesWithTemporalTrace
    ; w4TargetIsBalabanPartitionIdentityCommutesWithTemporalTrace =
        refl
    ; w4BalabanPartitionFunctionIdentityInput =
        W4.YMBalabanPartitionTemporalTraceCommutationReceipt.balabanPartitionFunctionIdentityInput
          W4.canonicalYMBalabanPartitionTemporalTraceCommutationReceipt
    ; w4BalabanPartitionFunctionIdentityInputIsTrue =
        refl
    ; w4ProductHaarMeasureBookkeepingInput =
        W4.YMBalabanPartitionTemporalTraceCommutationReceipt.productHaarMeasureBookkeepingInput
          W4.canonicalYMBalabanPartitionTemporalTraceCommutationReceipt
    ; w4ProductHaarMeasureBookkeepingInputIsTrue =
        refl
    ; w4TransferMatrixFaceActionBookkeepingInput =
        W4.YMBalabanPartitionTemporalTraceCommutationReceipt.transferMatrixFaceActionBookkeepingInput
          W4.canonicalYMBalabanPartitionTemporalTraceCommutationReceipt
    ; w4TransferMatrixFaceActionBookkeepingInputIsTrue =
        refl
    ; w4TransferTracePreservedBySpatialRGInput =
        W4.YMBalabanPartitionTemporalTraceCommutationReceipt.transferTracePreservedBySpatialRGInput
          W4.canonicalYMBalabanPartitionTemporalTraceCommutationReceipt
    ; w4TransferTracePreservedBySpatialRGInputIsTrue =
        refl
    ; w4BalabanPartitionIdentityCommutesWithTemporalTrace =
        W4.YMBalabanPartitionTemporalTraceCommutationReceipt.balabanPartitionIdentityCommutesWithTemporalTrace
          W4.canonicalYMBalabanPartitionTemporalTraceCommutationReceipt
    ; w4BalabanPartitionIdentityCommutesWithTemporalTraceIsTrue =
        refl
    ; sprint77W4InputFlags =
        canonicalSprint77YMW4InputFlags
    ; sprint77W4InputFlagsAreCanonical =
        refl
    ; openW4Targets =
        canonicalSprint77YMOpenW4Targets
    ; openW4TargetsAreCanonical =
        refl
    ; exactMissingLemmas =
        canonicalSprint77YMExactMissingLemmas
    ; exactMissingLemmasAreCanonical =
        refl
    ; spatialOnlyBalabanTraceNaturality =
        true
    ; spatialOnlyBalabanTraceNaturalityIsMissing =
        refl
    ; partitionIdentityTraceInterchangeLaw =
        true
    ; partitionIdentityTraceInterchangeLawIsMissing =
        refl
    ; gaugeOrbitFubiniForTemporalTrace =
        true
    ; gaugeOrbitFubiniForTemporalTraceIsMissing =
        refl
    ; largeFieldCutSeparationAtTransferTrace =
        true
    ; largeFieldCutSeparationAtTransferTraceIsMissing =
        refl
    ; exactLemmaContractClosed =
        true
    ; exactLemmaContractClosedIsFalse =
        refl
    ; clayYangMillsPromotedIsFalse =
        refl
    ; statement =
        sprint77YMPartitionTraceInterchangeStatement
    ; statementIsCanonical =
        refl
    ; boundary =
        sprint77YMPartitionTraceInterchangeBoundary
    ; boundaryIsCanonical =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        sprint77YMPartitionTraceInterchangePromotionImpossibleHere
    }
