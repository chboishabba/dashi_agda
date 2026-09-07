module DASHI.Law.SensibLawProviderAccessPolicyParityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Provider access/rate governance parity for the Rust online engine.
--
-- Rust is primary.  This module mirrors the implemented policy distinction:
--   provider-published guidance != SensibLaw self-imposed pacing != authority.
--
-- Inspection of the current HCA Terms of Use and FCA robots policy did not
-- disclose a numeric request-rate allowance.  That absence is represented as
-- unknown, not zero and not unlimited.  SensibLaw therefore retains its stricter
-- historical floor of one request per four seconds, burst one, unless a provider
-- publishes a stricter rule.
--
-- OALC is a bulk-snapshot/local-first lane.  AustLII ordinary automated case-law
-- access and JADE are not default live lanes in the current runtime.
------------------------------------------------------------------------

rustRepository : String
rustRepository = "chboishabba/slr"

rustBranch : String
rustBranch = "agent/governed-online-r6-v2"

rustSourceHead : String
rustSourceHead = "b530816215f0f437d46fab90827cc61d951cf727"

hcaPolicySource : String
hcaPolicySource = "https://www.hcourt.gov.au/terms-use"

fcaPolicySource : String
fcaPolicySource = "https://www.fedcourt.gov.au/robots.txt"

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

    providerPermissionAutomaticallySemanticAuthority : Bool
    providerPermissionAutomaticallySemanticAuthorityIsFalse :
      providerPermissionAutomaticallySemanticAuthority ≡ false

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
    false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data MissingRateMeansUnlimitedAccess : Set where
data ProviderPermissionMeansLegalAuthority : Set where
data RobotsAllowanceMeansSemanticPayment : Set where

aMissingRateDoesNotMeanUnlimitedAccess : MissingRateMeansUnlimitedAccess → ⊥
aMissingRateDoesNotMeanUnlimitedAccess ()

providerPermissionDoesNotMeanLegalAuthority : ProviderPermissionMeansLegalAuthority → ⊥
providerPermissionDoesNotMeanLegalAuthority ()

robotsAllowanceDoesNotMeanSemanticPayment : RobotsAllowanceMeansSemanticPayment → ⊥
robotsAllowanceDoesNotMeanSemanticPayment ()
