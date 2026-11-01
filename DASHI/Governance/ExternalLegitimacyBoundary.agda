module DASHI.Governance.ExternalLegitimacyBoundary where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Promotion.AuthorityGateCore as AuthorityGate

------------------------------------------------------------------------
-- External popular-legitimacy boundary.
--
-- A repository artifact may prove properties of a typed representation model.
-- It cannot thereby prove that a real constituency recognizes a representative,
-- that a constitution is legally operative, or that a transition is legitimate.
------------------------------------------------------------------------

data ExternalPopularRecognitionToken : Set where

data FormalReceiptSource : Set where
  localTypecheckingReceipt : FormalReceiptSource
  localRegressionReceipt : FormalReceiptSource
  localSourceCitationReceipt : FormalReceiptSource

data LegitimacySource : Set where
  formalReceiptLegitimacySource : FormalReceiptSource → LegitimacySource
  externalPopularRecognitionSource : LegitimacySource
  operativeConstitutionalSource : LegitimacySource

sourceCreatesPopularLegitimacy : LegitimacySource → Bool
sourceCreatesPopularLegitimacy (formalReceiptLegitimacySource source) = false
sourceCreatesPopularLegitimacy externalPopularRecognitionSource = true
sourceCreatesPopularLegitimacy operativeConstitutionalSource = true

formalReceiptDoesNotCreatePopularLegitimacy :
  ∀ source →
  sourceCreatesPopularLegitimacy
    (formalReceiptLegitimacySource source)
  ≡ false
formalReceiptDoesNotCreatePopularLegitimacy source = refl

record ExternalRecognitionClaim : Set where
  constructor externalRecognitionClaim
  field
    constituencyLabel : String
    representativeLabel : String
    recognitionToken : ExternalPopularRecognitionToken
    recognitionScope : String

open ExternalRecognitionClaim public

record LegitimacyBoundary : Set where
  constructor legitimacyBoundary
  field
    localTypecheckingCreatesPopularLegitimacy : Bool
    localRegressionCreatesPopularLegitimacy : Bool
    sourceCitationCreatesPopularLegitimacy : Bool
    externalRecognitionTokenAvailableInternally : Bool
    operativeConstitutionAvailableInternally : Bool
    politicalAuthorityPromoted : Bool
    legalAuthorityPromoted : Bool

canonicalLegitimacyBoundary : LegitimacyBoundary
canonicalLegitimacyBoundary =
  legitimacyBoundary
    false
    false
    false
    false
    false
    false
    false

legalAuthorityGateRemainsClosed :
  AuthorityGate.promoted AuthorityGate.legalPromotionGate ≡ false
legalAuthorityGateRemainsClosed =
  AuthorityGate.promotedIsFalse AuthorityGate.legalPromotionGate

legalExternalAuthorityRemainsAbsent :
  AuthorityGate.externalAuthoritySupplied AuthorityGate.legalPromotionGate
  ≡ false
legalExternalAuthorityRemainsAbsent =
  AuthorityGate.externalAuthoritySuppliedIsFalse
    AuthorityGate.legalPromotionGate

canonicalExternalLegitimacyBoundaryReceipt :
  GenericReceipt.GenericReceipt
canonicalExternalLegitimacyBoundaryReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "external popular legitimacy boundary"
    "DASHI.Governance.ExternalLegitimacyBoundary"
    "canonicalLegitimacyBoundary"
    "separates local typechecking, regression and citation receipts from external constituency recognition and operative constitutional authority"
    "no external popular-recognition token or operative constitutional artifact is supplied inside the repository"
    "agda -i . DASHI/Governance/ExternalLegitimacyBoundary.agda"
