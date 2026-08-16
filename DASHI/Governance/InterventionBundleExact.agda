module DASHI.Governance.InterventionBundleExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Intervention-bundle identification.
--
-- A result for one intervention bundle is not definitionally a result for a
-- different bundle.  The finite countermodel below makes the failure of that
-- transport kernel-visible rather than leaving it as prose.
------------------------------------------------------------------------

data SupportFeature : Set where
  punitiveConstraintRemoved : SupportFeature
  housingSupport : SupportFeature
  regulatedSupplyOrSafety : SupportFeature
  treatmentOrSocialSupport : SupportFeature

data InterventionBundle : Set where
  underprovisioned : InterventionBundle
  supported : InterventionBundle

data Outcome : Set where
  fails : Outcome
  succeeds : Outcome

enabled : InterventionBundle → SupportFeature → Bool
enabled underprovisioned punitiveConstraintRemoved = true
enabled underprovisioned housingSupport = false
enabled underprovisioned regulatedSupplyOrSafety = false
enabled underprovisioned treatmentOrSocialSupport = false
enabled supported punitiveConstraintRemoved = true
enabled supported housingSupport = true
enabled supported regulatedSupplyOrSafety = true
enabled supported treatmentOrSocialSupport = true

evaluate : InterventionBundle → Outcome
evaluate underprovisioned = fails
evaluate supported = succeeds

underprovisionedFails : evaluate underprovisioned ≡ fails
underprovisionedFails = refl

supportedSucceeds : evaluate supported ≡ succeeds
supportedSucceeds = refl

failsIsNotSucceeds : fails ≡ succeeds → ⊥
failsIsNotSucceeds ()

------------------------------------------------------------------------
-- Exact non-transport theorem:
--   Fail(underprovisioned) does not entail Fail(supported).
------------------------------------------------------------------------

failureTransportImpossible :
  (evaluate underprovisioned ≡ fails →
   evaluate supported ≡ fails) →
  ⊥
failureTransportImpossible transport =
  failsIsNotSucceeds
    (sym (transport underprovisionedFails))

------------------------------------------------------------------------
-- Generic bundle comparison keeps omissions explicit.
------------------------------------------------------------------------

record BundleSystem : Set₁ where
  field
    Feature : Set
    Bundle : Set
    OutcomeValue : Set
    enabledIn : Bundle → Feature → Set
    outcomeOf : Bundle → OutcomeValue

record BundleExtension
  (S : BundleSystem)
  (small large : BundleSystem.Bundle S) : Set₁ where
  field
    preservesEnabled :
      (feature : BundleSystem.Feature S) →
      BundleSystem.enabledIn S small feature →
      BundleSystem.enabledIn S large feature

record OmittedSupport
  (S : BundleSystem)
  (small large : BundleSystem.Bundle S) : Set₁ where
  field
    feature : BundleSystem.Feature S
    presentInLarge : BundleSystem.enabledIn S large feature
    absentInSmall : BundleSystem.enabledIn S small feature → ⊥

record InterventionIdentificationBoundary : Set where
  constructor interventionIdentificationBoundary
  field
    oneBundleOutcomeTransfersToAllSupersets : Bool
    omittedSupportsMustBeRepresented : Bool
    failedPartialReformRefutesSupportedReform : Bool
    namedPolicyNeedsEmpiricalInstantiation : Bool

canonicalInterventionIdentificationBoundary : InterventionIdentificationBoundary
canonicalInterventionIdentificationBoundary =
  interventionIdentificationBoundary false true false true
