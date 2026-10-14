module DASHI.Governance.IRISDenaMaxCutSourceGuardExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Governance.IRISDenaHansardCorrectionAwareEvidenceExact as Hansard
import DASHI.Governance.IRISDenaCorrectionAwareReviewGateExact as ReviewGate
import DASHI.Governance.AUKUSEmbeddedAuthorityCommandNoncollapseExact as Authority
import DASHI.Governance.IRISDenaMinisterialBriefingFOIBoundaryExact as Briefing

record SourceGuard : Set where
  constructor source-guard
  field
    hansardIdentityPrimary : Bool
    hansardIdentityPrimaryIsTrue : hansardIdentityPrimary ≡ true
    hansardDutyContentPrimaryPaid : Bool
    hansardDutyContentPrimaryPaidIsFalse : hansardDutyContentPrimaryPaid ≡ false
    hansardExactReviewBindingPaid : Bool
    hansardExactReviewBindingPaidIsFalse : hansardExactReviewBindingPaid ≡ false
    directiveExcerptSecondary : Bool
    directiveExcerptSecondaryIsTrue : directiveExcerptSecondary ≡ true
    directivePrimaryPaid : Bool
    directivePrimaryPaidIsFalse : directivePrimaryPaid ≡ false
    briefingFOISecondary : Bool
    briefingFOISecondaryIsTrue : briefingFOISecondary ≡ true
    briefingFOIPrimaryPaid : Bool
    briefingFOIPrimaryPaidIsFalse : briefingFOIPrimaryPaid ≡ false
    reviewMayUpgradeSourceAuthority : Bool
    reviewMayUpgradeSourceAuthorityIsFalse : reviewMayUpgradeSourceAuthority ≡ false
    reviewMayCreateHistoricalTruth : Bool
    reviewMayCreateHistoricalTruthIsFalse : reviewMayCreateHistoricalTruth ≡ false
    paretoMayUpgradeAuthority : Bool
    paretoMayUpgradeAuthorityIsFalse : paretoMayUpgradeAuthority ≡ false

open SourceGuard public

canonicalGuard : SourceGuard
canonicalGuard =
  source-guard
    true refl
    false refl
    false refl
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl

hansardBundle : Hansard.CorrectionAwarePrimaryBundle
hansardBundle = Hansard.canonicalPrimaryBundle

hansardReviewDemand : ReviewGate.CorrectionAwareReviewDemand
hansardReviewDemand = ReviewGate.canonicalReviewDemand

directiveReceipt : Authority.EmbeddedAuthorityReceipt
directiveReceipt = Authority.canonicalAuthorityReceipt

briefingReceipt : Briefing.MinisterialBriefingFOIReceipt
briefingReceipt = Briefing.canonicalReceipt

data ParetoPriorityUpgradesSourceAuthority : Set where
data SecondaryExcerptBecomesPrimaryByCorroboration : Set where
data HumanReviewUpgradesSourceAuthority : Set where
data HumanReviewCreatesHistoricalTruth : Set where

paretoPriorityDoesNotUpgradeAuthority :
  ParetoPriorityUpgradesSourceAuthority → ⊥
paretoPriorityDoesNotUpgradeAuthority ()

secondaryExcerptDoesNotBecomePrimaryByCorroboration :
  SecondaryExcerptBecomesPrimaryByCorroboration → ⊥
secondaryExcerptDoesNotBecomePrimaryByCorroboration ()

humanReviewDoesNotUpgradeSourceAuthority :
  HumanReviewUpgradesSourceAuthority → ⊥
humanReviewDoesNotUpgradeSourceAuthority ()

humanReviewDoesNotCreateHistoricalTruth :
  HumanReviewCreatesHistoricalTruth → ⊥
humanReviewDoesNotCreateHistoricalTruth ()
