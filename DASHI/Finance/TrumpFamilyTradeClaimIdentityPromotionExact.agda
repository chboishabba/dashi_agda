module DASHI.Finance.TrumpFamilyTradeClaimIdentityPromotionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- TRADE-CLAIM SAME-OBJECT PROMOTION GATE
--
-- A source citation, matching subject name, or matching disclosure document is
-- not enough to identify one underlying transaction. Promotion requires the
-- exact consumed coordinates plus a same-object receipt. This is the trade
-- analogue of the repository's observable-identity gates.
------------------------------------------------------------------------

record ExactTransactionCoordinates
    (left right : Atlas.TradeEvidenceClaim) : Set₁ where
  constructor exact-transaction-coordinates
  field
    subjectMatches : Atlas.subject left ≡ Atlas.subject right
    objectMatches : Atlas.issuerOrObject left ≡ Atlas.issuerOrObject right
    claimKindMatches : Atlas.claimKind left ≡ Atlas.claimKind right
    eventDateMatches : Atlas.eventDate left ≡ Atlas.eventDate right
    transactionLocatorReference : String
    valueRoleReference : String
    sameUnderlyingTransactionReceipt : Set

open ExactTransactionCoordinates public

record ClaimPromotionGate
    (left right : Atlas.TradeEvidenceClaim) : Set₁ where
  constructor claim-promotion-gate
  field
    exactCoordinates : ExactTransactionCoordinates left right
    leftSupportScopeRetained : String
    rightSupportScopeRetained : String
    sourceIdentityReference : String
    promotionReference : String

open ClaimPromotionGate public

------------------------------------------------------------------------
-- Finite collision: two transaction rows can share one filer/document surface
-- while remaining different transaction identities. Therefore source/filer
-- equality alone cannot be a same-object promotion rule.
------------------------------------------------------------------------

data SyntheticRow : Set where
  rowA rowB : SyntheticRow

data SyntheticFiler : Set where
  sameFiler : SyntheticFiler

data SyntheticDisclosure : Set where
  sameDisclosure : SyntheticDisclosure

filerOf : SyntheticRow → SyntheticFiler
filerOf rowA = sameFiler
filerOf rowB = sameFiler

disclosureOf : SyntheticRow → SyntheticDisclosure
disclosureOf rowA = sameDisclosure
disclosureOf rowB = sameDisclosure

rowIdentityQuery : SyntheticRow → SyntheticRow
rowIdentityQuery x = x

sameFilerAcrossRows : filerOf rowA ≡ filerOf rowB
sameFilerAcrossRows = refl

sameDisclosureAcrossRows : disclosureOf rowA ≡ disclosureOf rowB
sameDisclosureAcrossRows = refl

rowsRemainDistinct : rowA ≡ rowB → ⊥
rowsRemainDistinct ()

record CoarseDocumentSurface : Set where
  constructor coarse-document-surface
  field
    filer : SyntheticFiler
    disclosure : SyntheticDisclosure

coarse : SyntheticRow → CoarseDocumentSurface
coarse rowA = coarse-document-surface sameFiler sameDisclosure
coarse rowB = coarse-document-surface sameFiler sameDisclosure

coarseRowsCollide : coarse rowA ≡ coarse rowB
coarseRowsCollide = refl

coarseDocumentSurfaceCannotRecoverTransactionIdentity :
  ((x y : SyntheticRow) → coarse x ≡ coarse y → rowIdentityQuery x ≡ rowIdentityQuery y) → ⊥
coarseDocumentSurfaceCannotRecoverTransactionIdentity factor =
  rowsRemainDistinct (factor rowA rowB coarseRowsCollide)

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SameSubjectMeansSameTransactionPermission : Set where
data SameDocumentMeansSameTransactionPermission : Set where
data SecondaryAgreementMeansSameObjectPermission : Set where
data SameObjectMeansCausationPermission : Set where
data SameObjectMeansIllegalityPermission : Set where

sameSubjectDoesNotIdentifyTransaction : SameSubjectMeansSameTransactionPermission → ⊥
sameSubjectDoesNotIdentifyTransaction ()

sameDocumentDoesNotIdentifyTransaction : SameDocumentMeansSameTransactionPermission → ⊥
sameDocumentDoesNotIdentifyTransaction ()

secondaryAgreementDoesNotIdentifySameObject : SecondaryAgreementMeansSameObjectPermission → ⊥
secondaryAgreementDoesNotIdentifySameObject ()

sameObjectDoesNotCreateCausation : SameObjectMeansCausationPermission → ⊥
sameObjectDoesNotCreateCausation ()

sameObjectDoesNotCreateIllegality : SameObjectMeansIllegalityPermission → ⊥
sameObjectDoesNotCreateIllegality ()

record TradeClaimIdentityPromotionBoundary : Set where
  constructor trade-claim-identity-promotion-boundary
  field
    sameSubjectInsufficient : Bool
    sameDisclosureInsufficient : Bool
    exactLocatorRequired : Bool
    valueRoleRequired : Bool
    sameObjectReceiptRequired : Bool
    sameObjectDoesNotCreateCausationOrIllegality : Bool

canonicalTradeClaimIdentityPromotionBoundary : TradeClaimIdentityPromotionBoundary
canonicalTradeClaimIdentityPromotionBoundary =
  trade-claim-identity-promotion-boundary true true true true true true
