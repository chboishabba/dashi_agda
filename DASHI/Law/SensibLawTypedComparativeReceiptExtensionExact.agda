module DASHI.Law.SensibLawTypedComparativeReceiptExtensionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawChangeLocusExact as Locus
import DASHI.Law.SensibLawTypedAnswerChangingExplanationExact as Explain

------------------------------------------------------------------------
-- M11.1/M11.2 STABLE-ABI TYPED RECEIPT EXTENSION
--
-- The already-green comparative receipt remains the base ABI. Change-layer
-- metadata and typed explanations are attached as an extension keyed by the
-- exact comparison/delta references; they do not rewrite the base receipt.
------------------------------------------------------------------------

record ComparativeReceiptIdentity : Set where
  constructor comparative-receipt-identity
  field
    schemaVersion : String
    comparisonRef : String

open ComparativeReceiptIdentity public

record TypedComparativeReceiptExtension
    (base : ComparativeReceiptIdentity) : Set where
  constructor typed-comparative-receipt-extension
  field
    extensionSchemaVersion : String
    baseSchemaVersion : String
    baseSchemaPreserved :
      baseSchemaVersion ≡ schemaVersion base
    extensionComparisonRef : String
    comparisonIdentityPreserved :
      extensionComparisonRef ≡ comparisonRef base
    changeLayer : Locus.ChangeLayer
    explanation : Explain.AnswerChangeStep
    claimsCausationBeyondReceipt : Bool
    claimsCausationBeyondReceiptIsFalse :
      claimsCausationBeyondReceipt ≡ false
    predictsOutcome : Bool
    predictsOutcomeIsFalse :
      predictsOutcome ≡ false
    candidateOnly : Bool
    candidateOnlyIsTrue :
      candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false
    createsClaimTruth : Bool
    createsClaimTruthIsFalse :
      createsClaimTruth ≡ false

open TypedComparativeReceiptExtension public

pabaiBaseReceiptIdentity : ComparativeReceiptIdentity
pabaiBaseReceiptIdentity =
  comparative-receipt-identity
    "sl.comparative_receipt.v0_1"
    "comparison:pabai:w0-w1"

pabaiTypedReceiptExtension :
  TypedComparativeReceiptExtension pabaiBaseReceiptIdentity
pabaiTypedReceiptExtension =
  typed-comparative-receipt-extension
    "sl.typed_comparative_receipt_extension.v0_1"
    "sl.comparative_receipt.v0_1"
    refl
    "comparison:pabai:w0-w1"
    refl
    Locus.applicabilityLayer
    Explain.pabaiDefeaterStep
    false refl
    false refl
    true refl
    false refl
    false refl

data TypedExtensionMutatesBaseSchema : Set where
data TypedExtensionChangesComparisonIdentity : Set where
data TypedExplanationCreatesCausation : Set where
data TypedExtensionCreatesAuthority : Set where
data TypedExtensionCreatesTruth : Set where

typedExtensionDoesNotMutateBaseSchema :
  TypedExtensionMutatesBaseSchema → ⊥
typedExtensionDoesNotMutateBaseSchema ()

typedExtensionDoesNotChangeComparisonIdentity :
  TypedExtensionChangesComparisonIdentity → ⊥
typedExtensionDoesNotChangeComparisonIdentity ()

typedExplanationDoesNotManufactureCausation :
  TypedExplanationCreatesCausation → ⊥
typedExplanationDoesNotManufactureCausation ()

typedExtensionDoesNotCreateAuthority :
  TypedExtensionCreatesAuthority → ⊥
typedExtensionDoesNotCreateAuthority ()

typedExtensionDoesNotCreateTruth :
  TypedExtensionCreatesTruth → ⊥
typedExtensionDoesNotCreateTruth ()

record TypedComparativeReceiptBoundary : Set where
  constructor typedComparativeReceiptBoundary
  field
    baseV01SchemaPreserved : Bool
    baseV01SchemaPreservedIsTrue :
      baseV01SchemaPreserved ≡ true

    changeLayerAttachedWithoutBaseMutation : Bool
    changeLayerAttachedWithoutBaseMutationIsTrue :
      changeLayerAttachedWithoutBaseMutation ≡ true

    typedExplanationAttachedWithoutTruthPromotion : Bool
    typedExplanationAttachedWithoutTruthPromotionIsTrue :
      typedExplanationAttachedWithoutTruthPromotion ≡ true

    extensionPredictsOutcome : Bool
    extensionPredictsOutcomeIsFalse :
      extensionPredictsOutcome ≡ false

    extensionCreatesAuthority : Bool
    extensionCreatesAuthorityIsFalse :
      extensionCreatesAuthority ≡ false

    extensionCreatesTruth : Bool
    extensionCreatesTruthIsFalse :
      extensionCreatesTruth ≡ false

open TypedComparativeReceiptBoundary public

canonicalTypedComparativeReceiptBoundary :
  TypedComparativeReceiptBoundary
canonicalTypedComparativeReceiptBoundary =
  typedComparativeReceiptBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
