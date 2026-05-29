module DASHI.Physics.QFT.NonabelianGapNarrowedReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Narrowed nonabelian gap receipt.
--
-- This receipt intentionally does not promote G_DHR ~= G_SM.  It records the
-- narrowed residual work as three precise mathematical questions: SU3_c must
-- be supplied by nonabelian sector generation rather than by the finite CM
-- character group; U1_Y must extend the finite Z/3/Z6 action continuously; and
-- SU2_L is conditional on deriving a Clifford/Dirac spin sector from the
-- carrier.

data NarrowedNonabelianGapQuestion : Set where
  su3ColourDepthTwoOctetQuestion :
    NarrowedNonabelianGapQuestion

  u1HyperchargeContinuousExtensionQuestion :
    NarrowedNonabelianGapQuestion

  su2WeakSpinCarrierDerivationQuestion :
    NarrowedNonabelianGapQuestion

canonicalNarrowedNonabelianGapQuestions :
  List NarrowedNonabelianGapQuestion
canonicalNarrowedNonabelianGapQuestions =
  su3ColourDepthTwoOctetQuestion
  ∷ u1HyperchargeContinuousExtensionQuestion
  ∷ su2WeakSpinCarrierDerivationQuestion
  ∷ []

su3QuestionStatement : String
su3QuestionStatement =
  "SU3_c is not present in the finite CM character group; which depth-2 tensor products of carrier sectors contain an 8-dimensional colour sector?"

u1yQuestionStatement : String
u1yQuestionStatement =
  "U1_Y requires a continuous extension of the finite Z/3 and Z6 action; what is the canonical compact-continuous completion and hypercharge normalization?"

su2QuestionStatement : String
su2QuestionStatement =
  "SU2_L is conditional on deriving the Clifford/Dirac spin sector from the carrier; which carrier construction yields Rep(SU2) with the weak doublet sector?"

finiteCMCharacterGroupLabel : String
finiteCMCharacterGroupLabel =
  "Z/4 x Z/6 x Z/2"

su3CanonicalRequiredSectorDimension : Nat
su3CanonicalRequiredSectorDimension =
  8

su3CanonicalRequiredTensorDepth : Nat
su3CanonicalRequiredTensorDepth =
  2

u1yFiniteActionLabel : String
u1yFiniteActionLabel =
  "Z/3/Z6"

u1yTargetContinuousGroupLabel : String
u1yTargetContinuousGroupLabel =
  "U(1)_Y"

su2ConditionalSourceLabel : String
su2ConditionalSourceLabel =
  "carrier-derived Clifford/Dirac spin sector"

su2TargetSectorLabel : String
su2TargetSectorLabel =
  "Rep(SU2_L)"

record NonabelianGapNarrowedReceipt : Setω where
  field
    narrowedQuestions :
      List NarrowedNonabelianGapQuestion

    narrowedQuestionsAreCanonical :
      narrowedQuestions ≡ canonicalNarrowedNonabelianGapQuestions

    su3Question :
      String

    su3QuestionIsCanonical :
      su3Question ≡ su3QuestionStatement

    su3CMCharacterGroup :
      String

    su3CMCharacterGroupIsFiniteCM :
      su3CMCharacterGroup ≡ finiteCMCharacterGroupLabel

    su3MissingFromCMCharacterGroup :
      Bool

    su3MissingFromCMCharacterGroupIsTrue :
      su3MissingFromCMCharacterGroup ≡ true

    su3DepthTwoTensorProductsRequired :
      Bool

    su3DepthTwoTensorProductsRequiredIsTrue :
      su3DepthTwoTensorProductsRequired ≡ true

    su3RequiredTensorDepth :
      Nat

    su3RequiredTensorDepthIsTwo :
      su3RequiredTensorDepth
      ≡
      su3CanonicalRequiredTensorDepth

    su3EightDimensionalSectorRequired :
      Bool

    su3EightDimensionalSectorRequiredIsTrue :
      su3EightDimensionalSectorRequired ≡ true

    su3RequiredSectorDimension :
      Nat

    su3RequiredSectorDimensionIsEight :
      su3RequiredSectorDimension
      ≡
      su3CanonicalRequiredSectorDimension

    u1yQuestion :
      String

    u1yQuestionIsCanonical :
      u1yQuestion ≡ u1yQuestionStatement

    u1yFiniteAction :
      String

    u1yFiniteActionIsCanonical :
      u1yFiniteAction ≡ u1yFiniteActionLabel

    u1yContinuousExtensionRequired :
      Bool

    u1yContinuousExtensionRequiredIsTrue :
      u1yContinuousExtensionRequired ≡ true

    u1yContinuousTarget :
      String

    u1yContinuousTargetIsCanonical :
      u1yContinuousTarget ≡ u1yTargetContinuousGroupLabel

    su2Question :
      String

    su2QuestionIsCanonical :
      su2Question ≡ su2QuestionStatement

    su2ConditionalOnCarrierSpinSector :
      Bool

    su2ConditionalOnCarrierSpinSectorIsTrue :
      su2ConditionalOnCarrierSpinSector ≡ true

    su2CarrierSpinSource :
      String

    su2CarrierSpinSourceIsCanonical :
      su2CarrierSpinSource ≡ su2ConditionalSourceLabel

    su2TargetSector :
      String

    su2TargetSectorIsCanonical :
      su2TargetSector ≡ su2TargetSectorLabel

    receiptNonabelianGapNarrowed :
      Bool

    receiptNonabelianGapNarrowedIsTrue :
      receiptNonabelianGapNarrowed ≡ true

    receiptSU3QuestionRecorded :
      Bool

    receiptSU3QuestionRecordedIsTrue :
      receiptSU3QuestionRecorded ≡ true

    receiptU1YQuestionRecorded :
      Bool

    receiptU1YQuestionRecordedIsTrue :
      receiptU1YQuestionRecorded ≡ true

    receiptSU2QuestionRecorded :
      Bool

    receiptSU2QuestionRecordedIsTrue :
      receiptSU2QuestionRecorded ≡ true

    receiptGDHREqualsGSMPromoted :
      Bool

    receiptGDHREqualsGSMPromotedIsFalse :
      receiptGDHREqualsGSMPromoted ≡ false

    receiptBoundary :
      List String

open NonabelianGapNarrowedReceipt public

canonicalNonabelianGapNarrowedReceipt :
  NonabelianGapNarrowedReceipt
canonicalNonabelianGapNarrowedReceipt =
  record
    { narrowedQuestions =
        canonicalNarrowedNonabelianGapQuestions
    ; narrowedQuestionsAreCanonical =
        refl
    ; su3Question =
        su3QuestionStatement
    ; su3QuestionIsCanonical =
        refl
    ; su3CMCharacterGroup =
        finiteCMCharacterGroupLabel
    ; su3CMCharacterGroupIsFiniteCM =
        refl
    ; su3MissingFromCMCharacterGroup =
        true
    ; su3MissingFromCMCharacterGroupIsTrue =
        refl
    ; su3DepthTwoTensorProductsRequired =
        true
    ; su3DepthTwoTensorProductsRequiredIsTrue =
        refl
    ; su3RequiredTensorDepth =
        su3CanonicalRequiredTensorDepth
    ; su3RequiredTensorDepthIsTwo =
        refl
    ; su3EightDimensionalSectorRequired =
        true
    ; su3EightDimensionalSectorRequiredIsTrue =
        refl
    ; su3RequiredSectorDimension =
        su3CanonicalRequiredSectorDimension
    ; su3RequiredSectorDimensionIsEight =
        refl
    ; u1yQuestion =
        u1yQuestionStatement
    ; u1yQuestionIsCanonical =
        refl
    ; u1yFiniteAction =
        u1yFiniteActionLabel
    ; u1yFiniteActionIsCanonical =
        refl
    ; u1yContinuousExtensionRequired =
        true
    ; u1yContinuousExtensionRequiredIsTrue =
        refl
    ; u1yContinuousTarget =
        u1yTargetContinuousGroupLabel
    ; u1yContinuousTargetIsCanonical =
        refl
    ; su2Question =
        su2QuestionStatement
    ; su2QuestionIsCanonical =
        refl
    ; su2ConditionalOnCarrierSpinSector =
        true
    ; su2ConditionalOnCarrierSpinSectorIsTrue =
        refl
    ; su2CarrierSpinSource =
        su2ConditionalSourceLabel
    ; su2CarrierSpinSourceIsCanonical =
        refl
    ; su2TargetSector =
        su2TargetSectorLabel
    ; su2TargetSectorIsCanonical =
        refl
    ; receiptNonabelianGapNarrowed =
        true
    ; receiptNonabelianGapNarrowedIsTrue =
        refl
    ; receiptSU3QuestionRecorded =
        true
    ; receiptSU3QuestionRecordedIsTrue =
        refl
    ; receiptU1YQuestionRecorded =
        true
    ; receiptU1YQuestionRecordedIsTrue =
        refl
    ; receiptSU2QuestionRecorded =
        true
    ; receiptSU2QuestionRecordedIsTrue =
        refl
    ; receiptGDHREqualsGSMPromoted =
        false
    ; receiptGDHREqualsGSMPromotedIsFalse =
        refl
    ; receiptBoundary =
        "The nonabelian gap is narrowed to exactly three recorded mathematical questions"
        ∷ "SU3_c remains absent from the finite CM character group Z/4 x Z/6 x Z/2 and requires depth-2 tensor products containing an 8-dimensional sector"
        ∷ "U1_Y requires a continuous extension of the finite Z/3/Z6 action"
        ∷ "SU2_L remains conditional on deriving the Clifford/Dirac spin sector from the carrier"
        ∷ "No G_DHR ~= G_SM promotion is made by this receipt"
        ∷ []
    }

nonabelianGapNarrowed :
  Bool
nonabelianGapNarrowed =
  NonabelianGapNarrowedReceipt.receiptNonabelianGapNarrowed
    canonicalNonabelianGapNarrowedReceipt

nonabelianGapNarrowedIsTrue :
  nonabelianGapNarrowed ≡ true
nonabelianGapNarrowedIsTrue =
  refl

su3QuestionRecorded :
  Bool
su3QuestionRecorded =
  NonabelianGapNarrowedReceipt.receiptSU3QuestionRecorded
    canonicalNonabelianGapNarrowedReceipt

su3QuestionRecordedIsTrue :
  su3QuestionRecorded ≡ true
su3QuestionRecordedIsTrue =
  refl

u1yQuestionRecorded :
  Bool
u1yQuestionRecorded =
  NonabelianGapNarrowedReceipt.receiptU1YQuestionRecorded
    canonicalNonabelianGapNarrowedReceipt

u1yQuestionRecordedIsTrue :
  u1yQuestionRecorded ≡ true
u1yQuestionRecordedIsTrue =
  refl

su2QuestionRecorded :
  Bool
su2QuestionRecorded =
  NonabelianGapNarrowedReceipt.receiptSU2QuestionRecorded
    canonicalNonabelianGapNarrowedReceipt

su2QuestionRecordedIsTrue :
  su2QuestionRecorded ≡ true
su2QuestionRecordedIsTrue =
  refl

gDHREqualsGSMPromoted :
  Bool
gDHREqualsGSMPromoted =
  NonabelianGapNarrowedReceipt.receiptGDHREqualsGSMPromoted
    canonicalNonabelianGapNarrowedReceipt

gDHREqualsGSMPromotedIsFalse :
  gDHREqualsGSMPromoted ≡ false
gDHREqualsGSMPromotedIsFalse =
  refl

nonabelianGapNarrowedQuestionsAreCanonical :
  narrowedQuestions canonicalNonabelianGapNarrowedReceipt
  ≡
  canonicalNarrowedNonabelianGapQuestions
nonabelianGapNarrowedQuestionsAreCanonical =
  refl
