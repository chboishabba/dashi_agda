module DASHI.Economics.SituatedInformationAccessFabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- SITUATED INFORMATION ACCESS FABRIC
--
-- Discussion-origin architecture: Johl Brown, 2026-09-17.
-- The proposal separates information identity from access event, capability,
-- contract, quote, delivery and realised outcome, and treats effective access
-- as situated across economic/technical/accessibility/privacy/legal/temporal
-- coordinates.  The typed carrier and finite firewalls below are DASHI
-- formal synthesis.  No external technology or JMD repository is assigned
-- ownership of these DASHI theorems by structural analogy.
------------------------------------------------------------------------

record InformationObject : Set where
  constructor informationObject
  field
    objectIdentity : String
    publicationTime : String
    provenanceIdentity : String

open InformationObject public

record SituatedAccessContext : Set where
  constructor situatedAccessContext
  field
    requester : String
    principal : String
    agent : String
    purpose : String
    monetaryZeroPrice : Bool
    networkReachable : Bool
    bandwidthAdequate : Bool
    deviceCompatible : Bool
    assistiveAccessible : Bool
    languageAccessible : Bool
    identityDisclosureRequired : Bool
    surveillanceBurdenPresent : Bool
    geographicGatePresent : Bool
    openLicence : Bool
    reusePermitted : Bool
    machineReadable : Bool
    apiAccessible : Bool
    temporallyRelevant : Bool
    writeAuthorized : Bool
    commercialRole : Bool

open SituatedAccessContext public

record AccessPath : Set where
  constructor accessPath
  field
    underlyingInformation : InformationObject
    pathIdentity : String
    context : SituatedAccessContext
    latencyClass : String
    capacityClass : String
    slaClass : String
    priceClass : String
    publicCommonsPath : Bool
    premiumCapabilityPath : Bool
    effectiveAccessObserved : Bool

open AccessPath public

data ContractLifecycle : Set where
  quotedState : ContractLifecycle
  authorizedState : ContractLifecycle
  provisionedState : ContractLifecycle
  deliveredState : ContractLifecycle
  measuredState : ContractLifecycle
  settledState : ContractLifecycle

record AccessEvent : Set where
  constructor accessEvent
  field
    path : AccessPath
    lifecycle : ContractLifecycle
    eventReceipt : String

open AccessEvent public

record ReactionLatencyPath : Set where
  constructor reactionLatencyPath
  field
    detectionLatency : String
    decisionLatency : String
    actionLatency : String
    totalLatency : String
    decompositionDeclared : Bool

open ReactionLatencyPath public

------------------------------------------------------------------------
-- Public/common and premium capability paths may expose the same immutable
-- information object while differing in access capability.  Scarcity therefore
-- need not be manufactured by making the information object itself exclusive.
------------------------------------------------------------------------

exampleInformation : InformationObject
exampleInformation =
  informationObject
    "cid:example-information-object"
    "2026-09-17"
    "synthetic DASHI fixture"

publicContext : SituatedAccessContext
publicContext =
  situatedAccessContext
    "public requester"
    "public principal"
    "browser-or-assistive-agent"
    "ordinary public retrieval"
    true true true true true true
    false false false
    true true true false true
    false false

premiumContext : SituatedAccessContext
premiumContext =
  situatedAccessContext
    "premium requester"
    "premium principal"
    "authorized research agent"
    "low-latency high-capacity retrieval"
    false true true true true true
    false false false
    true true true true true
    false true

publicPath : AccessPath
publicPath =
  accessPath
    exampleInformation
    "access-path:public"
    publicContext
    "ordinary latency"
    "ordinary capacity"
    "best effort"
    "zero monetary price"
    true false true

premiumPath : AccessPath
premiumPath =
  accessPath
    exampleInformation
    "access-path:premium"
    premiumContext
    "lower latency"
    "reserved capacity"
    "declared SLA"
    "priced capability"
    false true true

publicPremiumShareUnderlyingInformation :
  underlyingInformation publicPath ≡ underlyingInformation premiumPath
publicPremiumShareUnderlyingInformation = refl

publicAndPremiumAreDifferentPaths :
  pathIdentity publicPath ≡ "access-path:public"
publicAndPremiumAreDifferentPaths = refl

------------------------------------------------------------------------
-- A contract lifecycle event is not the information object and settlement is
-- not claim truth.
------------------------------------------------------------------------

exampleQuotedEvent : AccessEvent
exampleQuotedEvent = accessEvent premiumPath quotedState "receipt:quote-example"

exampleSettledEvent : AccessEvent
exampleSettledEvent = accessEvent premiumPath settledState "receipt:settlement-example"

------------------------------------------------------------------------
-- Non-collapse firewalls.
------------------------------------------------------------------------

data InformationObjectIsAccessEvent : Set where
data ZeroPriceImpliesEffectiveAccess : Set where
data PublicReachabilityImpliesEffectiveAccess : Set where
data OpenLicenceImpliesEffectiveAccess : Set where
data MachineClientImpliesCommercialRole : Set where
data WriteAuthorizationImpliesEffectiveAccess : Set where
data DetectionSLAImpliesEndToEndReaction : Set where
data SettledContractCreatesTruth : Set where
data AccessibleImpliesAuthorized : Set where
data AuthorizedImpliesDelivered : Set where

informationObjectIsNotAccessEvent : InformationObjectIsAccessEvent → ⊥
informationObjectIsNotAccessEvent ()

zeroPriceDoesNotImplyEffectiveAccess : ZeroPriceImpliesEffectiveAccess → ⊥
zeroPriceDoesNotImplyEffectiveAccess ()

publicReachabilityDoesNotImplyEffectiveAccess : PublicReachabilityImpliesEffectiveAccess → ⊥
publicReachabilityDoesNotImplyEffectiveAccess ()

openLicenceDoesNotImplyEffectiveAccess : OpenLicenceImpliesEffectiveAccess → ⊥
openLicenceDoesNotImplyEffectiveAccess ()

machineClientDoesNotImplyCommercialRole : MachineClientImpliesCommercialRole → ⊥
machineClientDoesNotImplyCommercialRole ()

writeAuthorizationDoesNotImplyEffectiveAccess : WriteAuthorizationImpliesEffectiveAccess → ⊥
writeAuthorizationDoesNotImplyEffectiveAccess ()

detectionSLADoesNotImplyEndToEndReaction : DetectionSLAImpliesEndToEndReaction → ⊥
detectionSLADoesNotImplyEndToEndReaction ()

settledContractDoesNotCreateTruth : SettledContractCreatesTruth → ⊥
settledContractDoesNotCreateTruth ()

accessibleDoesNotImplyAuthorized : AccessibleImpliesAuthorized → ⊥
accessibleDoesNotImplyAuthorized ()

authorizedDoesNotImplyDelivered : AuthorizedImpliesDelivered → ⊥
authorizedDoesNotImplyDelivered ()

attributionRule : String
attributionRule =
  "Johl Brown is attributed for the discussion-origin situated-access/access-path architecture. DASHI owns this typed reconstruction and its finite empty-type firewalls. External network/storage/settlement projects are precedents only; no protocol identity, licence, price, access event or settlement receipt creates claim truth or semantic authority."
