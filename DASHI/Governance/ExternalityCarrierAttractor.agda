module DASHI.Governance.ExternalityCarrierAttractor where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.TraumaExploitationAttractor as Trauma

------------------------------------------------------------------------
-- Underprovisioned reform / externality-carrier confusion.
--
-- A bounded intervention can fail in the presence of missing enabling
-- infrastructure.  Failure of that actual bundle does not establish failure
-- of a distinct counterfactual bundle with the missing supports supplied.
------------------------------------------------------------------------

record ReformSystem : Set₁ where
  field
    Condition : Set
    Reform : Set
    Support : Set
    Externality : Set
    Carrier : Set
    Intervention : Set

    applyReform : Reform → Condition → Condition
    addSupport : Support → Condition → Condition
    observeExternality : Condition → Externality
    visibleCarrier : Externality → Carrier
    punitiveIntervention : Carrier → Intervention

open ReformSystem public

record UnderprovisionedReform
  (S : ReformSystem) : Set₁ where
  field
    baseline : Condition S
    reform : Reform S
    MissingSupport : Set
    missingSupport : MissingSupport
    actualCondition : Condition S
    actualConditionIsReformOnly :
      applyReform S reform baseline ≡ actualCondition

record SupportedReformCounterfactual
  (S : ReformSystem)
  (U : UnderprovisionedReform S) : Set₁ where
  field
    support : Support S
    supportedCondition : Condition S
    supportApplied :
      addSupport S support
        (UnderprovisionedReform.actualCondition U)
      ≡ supportedCondition


data FailureOfUnderprovisionedReformEstablishesSupportedFailure : Set where

underprovisionedFailureDoesNotEstablishSupportedFailure :
  FailureOfUnderprovisionedReformEstablishesSupportedFailure → ⊥
underprovisionedFailureDoesNotEstablishSupportedFailure ()

------------------------------------------------------------------------
-- Externality carrier confusion.
--
-- A visible person/group/site carrying an externality is not thereby the
-- sufficient cause of the externality.
------------------------------------------------------------------------

record ExternalityCarrierConfusion
  (S : ReformSystem) : Set₁ where
  field
    condition : Condition S
    externality : Externality S
    carrier : Carrier S
    externalityObserved : observeExternality S condition ≡ externality
    carrierIsVisible : visibleCarrier S externality ≡ carrier


data VisibleCarrierEstablishesSufficientCause : Set where

visibleCarrierDoesNotEstablishSufficientCause :
  VisibleCarrierEstablishesSufficientCause → ⊥
visibleCarrierDoesNotEstablishSufficientCause ()

------------------------------------------------------------------------
-- Punitive restoration attractor.
------------------------------------------------------------------------

record PunitiveRestorationCycle
  (S : ReformSystem) : Set₁ where
  field
    condition : Condition S
    externality : Externality S
    carrier : Carrier S
    intervention : Intervention S
    externalityObserved : observeExternality S condition ≡ externality
    carrierSelected : visibleCarrier S externality ≡ carrier
    punishmentSelected : punitiveIntervention S carrier ≡ intervention

record MultiCauseSystem : Set₁ where
  field
    Cause : Set
    Outcome : Set
    contributes : Cause → Outcome → Set

record CausalCompression
  (S : MultiCauseSystem) : Set₁ where
  field
    causes : List (MultiCauseSystem.Cause S)
    selectedCause : MultiCauseSystem.Cause S
    outcome : MultiCauseSystem.Outcome S
    selectedCauseContributes : MultiCauseSystem.contributes S selectedCause outcome


data ContributionEstablishesSufficiency : Set where

contributionDoesNotEstablishSufficiency :
  ContributionEstablishesSufficiency → ⊥
contributionDoesNotEstablishSufficiency ()

------------------------------------------------------------------------
-- Cross-pollination with the existing historical recursion carrier.
-- The point is structural reproduction, not a diagnosis of any named policy.
------------------------------------------------------------------------

record ExternalityAttractorBridge
  (T : Trauma.TraumaExploitationSystem) : Set₁ where
  field
    receipt : Trauma.TraumaExploitationAttractorReceipt T
    systemReproductionPatternOnly : Bool
    namedPolicyConclusionRequiresExternalEvidence : Bool

record ExternalityCarrierBoundary : Set where
  constructor externalityCarrierBoundary
  field
    reformFailureIdentifiesFullIntervention : Bool
    visibleCarrierIsSufficientCause : Bool
    contributionIsSufficiency : Bool
    publicVisibilityEqualsUnderlyingPrevalence : Bool
    punitiveResponseEqualsStructuralRepair : Bool
    counterfactualBundleMustBeIdentified : Bool

canonicalExternalityCarrierBoundary : ExternalityCarrierBoundary
canonicalExternalityCarrierBoundary =
  externalityCarrierBoundary false false false false false true

record ExternalityCarrierReceipt : Set where
  constructor externalityCarrierReceipt
  field
    label : String
    boundary : ExternalityCarrierBoundary
    supportsDrugPolicyCaseWithoutSettlingIt : Bool
    supportsHomelessnessCaseWithoutSettlingIt : Bool
    supportsImmigrationCapacityCaseWithoutSettlingIt : Bool
    supportsOutgroupReificationCaseWithoutSettlingIt : Bool

canonicalExternalityCarrierReceipt : ExternalityCarrierReceipt
canonicalExternalityCarrierReceipt =
  externalityCarrierReceipt
    "underprovisioned reform / externality carrier attractor"
    canonicalExternalityCarrierBoundary
    true true true true
