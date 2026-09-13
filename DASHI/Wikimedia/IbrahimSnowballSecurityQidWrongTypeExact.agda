module DASHI.Wikimedia.IbrahimSnowballSecurityQidWrongTypeExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Discovery

------------------------------------------------------------------------
-- QID / WRONGTYPE REGRESSION: "SECURITY" IS POLYSEMOUS.
--
-- Current Wikidata identities inspected 2026-09-10:
--   security, freedom/resilience from harm  Q2526135
--   security, tradable financial asset      Q169489
--
-- Food security may navigate toward the former sense. A lexical match on
-- "security" must never silently substitute the latter financial instrument.
------------------------------------------------------------------------

securityFromHarmQid : Identity.ExternalIdentityDemand
securityFromHarmQid = Identity.mkOptionalIdentityDemand
  "Ibrahim food-security second-order walk"
  "security parent sense relevant to food-security navigation"
  "security as freedom/resilience from harm"
  Identity.wikidataQid
  (Identity.verified "Q2526135" "Wikidata identity inspected 2026-09-10")

financialSecurityQid : Identity.ExternalIdentityDemand
financialSecurityQid = Identity.mkOptionalIdentityDemand
  "Ibrahim QID WrongType regression"
  "homonymous but semantically different Wikidata item"
  "security as tradable financial asset"
  Identity.wikidataQid
  (Identity.verified "Q169489" "Wikidata identity inspected 2026-09-10")

data SecurityWordEqualsSecuritySense : Set where
data FoodSecurityParentEqualsFinancialSecurity : Set where
data SameLabelCreatesQidIdentity : Set where

securityWordDoesNotDetermineSense : SecurityWordEqualsSecuritySense → ⊥
securityWordDoesNotDetermineSense ()

foodSecurityDoesNotBecomeFinancialInstrument : FoodSecurityParentEqualsFinancialSecurity → ⊥
foodSecurityDoesNotBecomeFinancialInstrument ()

lexicalEqualityDoesNotCreateEntityIdentity : SameLabelCreatesQidIdentity → ⊥
lexicalEqualityDoesNotCreateEntityIdentity ()

record SecurityQidWrongTypeBoundary : Set where
  constructor security-qid-wrong-type-boundary
  field
    bothHomonymousQidsRetained : Bool
    qidSenseMustBeInspected : Bool
    lexicalMatchMayNotChooseEntity : Bool
    parentGraphMayNotSubstituteWrongSense : Bool
    externalIdentityCreatesNoDomainTruth : Bool
    presentSenseInventoryClaimedComplete : Bool
open SecurityQidWrongTypeBoundary public

canonicalSecurityQidWrongTypeBoundary : SecurityQidWrongTypeBoundary
canonicalSecurityQidWrongTypeBoundary = security-qid-wrong-type-boundary
  true true true true false false

discoveryBoundary : Discovery.SnowballDiscoveryBoundary
discoveryBoundary = Discovery.canonicalSnowballDiscoveryBoundary
