module DASHI.Governance.NarrativeStructureEvidenceAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Governance.LombardiNarrativeStructureAdapterExact as Narrative

------------------------------------------------------------------------
-- SHARED EVIDENCE-METHOD ABI
--
-- Mirrors the Epstein branch discipline without importing branch-only owners.
------------------------------------------------------------------------

data CaseIdentity : Set where
  australianColonialFinanceCase : CaseIdentity
  epsteinStyleCase : CaseIdentity
  bcciHistoricalCase : CaseIdentity

data MethodSourceRole : Set where
  directRecord : MethodSourceRole
  correspondence : MethodSourceRole
  fundingStatement : MethodSourceRole
  institutionalHistory : MethodSourceRole
  investigativeFinding : MethodSourceRole
  artworkObservation : MethodSourceRole

data PromotionCeiling : Set where
  presenceOnly : PromotionCeiling
  boundedHistoricalClaim : PromotionCeiling
  directTransactionClaim : PromotionCeiling
  settlementClaim : PromotionCeiling
  wrongdoingClaim : PromotionCeiling

record EvidenceMethodReceipt : Set where
  constructor evidence-method-receipt
  field
    caseIdentity : CaseIdentity
    exactSourceIdentity : String
    sourceRole : MethodSourceRole
    boundedClaim : String
    promotionCeiling : PromotionCeiling
open EvidenceMethodReceipt public

australianGoldMethodFixture : EvidenceMethodReceipt
australianGoldMethodFixture = evidence-method-receipt
  australianColonialFinanceCase
  "NPG/ADB/Rothschild Archive claim-local source identity"
  institutionalHistory
  "Historical gold/finance claim remains bounded by the exact source receipt."
  boundedHistoricalClaim

epsteinMethodFixture : EvidenceMethodReceipt
epsteinMethodFixture = evidence-method-receipt
  epsteinStyleCase
  "EFTA-style exact document identity"
  correspondence
  "Document identity, role and bounded source claim are distinct from participation, settlement, purpose or wrongdoing."
  boundedHistoricalClaim

bcciMethodFixture : EvidenceMethodReceipt
bcciMethodFixture = evidence-method-receipt
  bcciHistoricalCase
  "Senate BCCI investigation / Whitney artwork identities"
  investigativeFinding
  "Investigative finding and artwork observation are separate evidence roles."
  boundedHistoricalClaim

data SharedEvidenceMethodCreatesSharedHistoricalNetwork : Set where
data SameSourceRoleCreatesSameClaimStrength : Set where
data BoundedClaimCreatesSettlement : Set where
data SourcePresenceCreatesWrongdoing : Set where

sharedEvidenceMethodDoesNotCreateSharedHistoricalNetwork :
  SharedEvidenceMethodCreatesSharedHistoricalNetwork → ⊥
sharedEvidenceMethodDoesNotCreateSharedHistoricalNetwork ()

sameSourceRoleDoesNotCreateSameClaimStrength : SameSourceRoleCreatesSameClaimStrength → ⊥
sameSourceRoleDoesNotCreateSameClaimStrength ()

boundedClaimDoesNotCreateSettlement : BoundedClaimCreatesSettlement → ⊥
boundedClaimDoesNotCreateSettlement ()

sourcePresenceDoesNotCreateWrongdoing : SourcePresenceCreatesWrongdoing → ⊥
sourcePresenceDoesNotCreateWrongdoing ()

record SharedMethodBoundary : Set where
  constructor shared-method-boundary
  field
    exactIdentityRequired : Bool
    sourceRoleSeparated : Bool
    boundedClaimSeparated : Bool
    promotionCeilingSeparated : Bool
    sharedMethodEqualsSharedNetwork : Bool
open SharedMethodBoundary public

canonicalSharedMethodBoundary : SharedMethodBoundary
canonicalSharedMethodBoundary = shared-method-boundary true true true true false
