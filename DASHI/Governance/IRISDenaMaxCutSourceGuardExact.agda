module DASHI.Governance.IRISDenaMaxCutSourceGuardExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Governance.IRISDenaHansardCorrectionAwareEvidenceExact as Hansard
import DASHI.Governance.AUKUSEmbeddedAuthorityCommandNoncollapseExact as Authority
import DASHI.Governance.IRISDenaMinisterialBriefingFOIBoundaryExact as Briefing

record SourceGuard : Set where
  constructor source-guard
  field
    hansardIdentityPrimary : Bool
    hansardIdentityPrimaryIsTrue : hansardIdentityPrimary ≡ true
    hansardDutyContentPrimaryPaid : Bool
    hansardDutyContentPrimaryPaidIsFalse : hansardDutyContentPrimaryPaid ≡ false
    directiveExcerptSecondary : Bool
    directiveExcerptSecondaryIsTrue : directiveExcerptSecondary ≡ true
    directivePrimaryPaid : Bool
    directivePrimaryPaidIsFalse : directivePrimaryPaid ≡ false
    briefingFOISecondary : Bool
    briefingFOISecondaryIsTrue : briefingFOISecondary ≡ true
    briefingFOIPrimaryPaid : Bool
    briefingFOIPrimaryPaidIsFalse : briefingFOIPrimaryPaid ≡ false
    paretoMayUpgradeAuthority : Bool
    paretoMayUpgradeAuthorityIsFalse : paretoMayUpgradeAuthority ≡ false

open SourceGuard public

canonicalGuard : SourceGuard
canonicalGuard =
  source-guard
    true refl
    false refl
    true refl
    false refl
    true refl
    false refl
    false refl

hansardBundle : Hansard.CorrectionAwarePrimaryBundle
hansardBundle = Hansard.canonicalPrimaryBundle

directiveReceipt : Authority.EmbeddedAuthorityReceipt
directiveReceipt = Authority.canonicalAuthorityReceipt

briefingReceipt : Briefing.MinisterialBriefingFOIReceipt
briefingReceipt = Briefing.canonicalReceipt

data ParetoPriorityUpgradesSourceAuthority : Set where
data SecondaryExcerptBecomesPrimaryByCorroboration : Set where

paretoPriorityDoesNotUpgradeAuthority :
  ParetoPriorityUpgradesSourceAuthority → ⊥
paretoPriorityDoesNotUpgradeAuthority ()

secondaryExcerptDoesNotBecomePrimaryByCorroboration :
  SecondaryExcerptBecomesPrimaryByCorroboration → ⊥
secondaryExcerptDoesNotBecomePrimaryByCorroboration ()
