module DASHI.Law.SensibLawProviderAccessPolicyParityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Provider access/rate/reuse governance parity for the Rust online engine.
-- Rust is primary. Provider-published guidance, SensibLaw pacing, reuse duties,
-- and semantic/legal authority remain distinct coordinates.
------------------------------------------------------------------------

rustRepository : String
rustRepository = "chboishabba/slr"

rustBranch : String
rustBranch = "agent/governed-online-r6-v2"

rustSourceHead : String
rustSourceHead = "d7ace6ec19bd44f7b6395702a5f0bdbd867d8f48"

hcaPolicySource : String
hcaPolicySource = "https://www.hcourt.gov.au/terms-use"

fcaAccessPolicySource : String
fcaAccessPolicySource = "https://www.fedcourt.gov.au/robots.txt"

fcaReusePolicySource : String
fcaReusePolicySource = "https://www.fedcourt.gov.au/copyright"

oalcPolicySource : String
oalcPolicySource = "https://huggingface.co/datasets/isaacus/open-australian-legal-corpus"

selfImposedMinimumIntervalSeconds : Nat
selfImposedMinimumIntervalSeconds = 4

selfImposedBurstLimit : Nat
selfImposedBurstLimit = 1

record ProviderAccessPolicyParityBoundary : Set where
  constructor providerAccessPolicyParityBoundary
  field
    hcaPublishedNumericRateKnown : Bool
    hcaPublishedNumericRateKnownIsFalse : hcaPublishedNumericRateKnown ≡ false

    fcaPublishedNumericRateKnown : Bool
    fcaPublishedNumericRateKnownIsFalse : fcaPublishedNumericRateKnown ≡ false

    missingPublishedNumericRateMeansUnlimited : Bool
    missingPublishedNumericRateMeansUnlimitedIsFalse :
      missingPublishedNumericRateMeansUnlimited ≡ false

    fourSecondSelfImposedFloorRetained : Bool
    fourSecondSelfImposedFloorRetainedIsTrue :
      fourSecondSelfImposedFloorRetained ≡ true

    burstOneRetained : Bool
    burstOneRetainedIsTrue : burstOneRetained ≡ true

    stricterProviderRuleWouldWin : Bool
    stricterProviderRuleWouldWinIsTrue : stricterProviderRuleWouldWin ≡ true

    weakerProviderRuleCannotRelaxSelfFloor : Bool
    weakerProviderRuleCannotRelaxSelfFloorIsTrue :
      weakerProviderRuleCannotRelaxSelfFloor ≡ true

    hcaBoundedLiveCacheFirst : Bool
    hcaBoundedLiveCacheFirstIsTrue : hcaBoundedLiveCacheFirst ≡ true

    fcaBoundedLiveCacheFirst : Bool
    fcaBoundedLiveCacheFirstIsTrue : fcaBoundedLiveCacheFirst ≡ true

    oalcBulkSnapshotLocalFirst : Bool
    oalcBulkSnapshotLocalFirstIsTrue : oalcBulkSnapshotLocalFirst ≡ true

    austliiDefaultLiveLaneEnabled : Bool
    austliiDefaultLiveLaneEnabledIsFalse : austliiDefaultLiveLaneEnabled ≡ false

    jadeDefaultLiveLaneEnabled : Bool
    jadeDefaultLiveLaneEnabledIsFalse : jadeDefaultLiveLaneEnabled ≡ false

    hcaAttributionRequired : Bool
    hcaAttributionRequiredIsTrue : hcaAttributionRequired ≡ true

    hcaOriginalSourceURLRequired : Bool
    hcaOriginalSourceURLRequiredIsTrue : hcaOriginalSourceURLRequired ≡ true

    hcaAccuracyOrUnalteredCopyRequired : Bool
    hcaAccuracyOrUnalteredCopyRequiredIsTrue :
      hcaAccuracyOrUnalteredCopyRequired ≡ true

    hcaNonMisleadingUseRequired : Bool
    hcaNonMisleadingUseRequiredIsTrue : hcaNonMisleadingUseRequired ≡ true

    fcaAttributionRequired : Bool
    fcaAttributionRequiredIsTrue : fcaAttributionRequired ≡ true

    fcaOriginalSourceURLRequired : Bool
    fcaOriginalSourceURLRequiredIsTrue : fcaOriginalSourceURLRequired ≡ true

    fcaAccuracyOrUnalteredCopyRequired : Bool
    fcaAccuracyOrUnalteredCopyRequiredIsTrue :
      fcaAccuracyOrUnalteredCopyRequired ≡ true

    thirdPartyRightsMayApply : Bool
    thirdPartyRightsMayApplyIsTrue : thirdPartyRightsMayApply ≡ true

    providerPermissionAutomaticallySemanticAuthority : Bool
    providerPermissionAutomaticallySemanticAuthorityIsFalse :
      providerPermissionAutomaticallySemanticAuthority ≡ false

    reusePermissionAutomaticallyCurrentAuthority : Bool
    reusePermissionAutomaticallyCurrentAuthorityIsFalse :
      reusePermissionAutomaticallyCurrentAuthority ≡ false

canonicalProviderAccessPolicyParityBoundary : ProviderAccessPolicyParityBoundary
canonicalProviderAccessPolicyParityBoundary =
  providerAccessPolicyParityBoundary
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data MissingRateMeansUnlimitedAccess : Set where
data ProviderPermissionMeansLegalAuthority : Set where
data ReusePermissionMeansCurrentAuthority : Set where
data RobotsAllowanceMeansSemanticPayment : Set where

missingRateDoesNotMeanUnlimitedAccess : MissingRateMeansUnlimitedAccess → ⊥
missingRateDoesNotMeanUnlimitedAccess ()

providerPermissionDoesNotMeanLegalAuthority : ProviderPermissionMeansLegalAuthority → ⊥
providerPermissionDoesNotMeanLegalAuthority ()

reusePermissionDoesNotMeanCurrentAuthority : ReusePermissionMeansCurrentAuthority → ⊥
reusePermissionDoesNotMeanCurrentAuthority ()

robotsAllowanceDoesNotMeanSemanticPayment : RobotsAllowanceMeansSemanticPayment → ⊥
robotsAllowanceDoesNotMeanSemanticPayment ()
