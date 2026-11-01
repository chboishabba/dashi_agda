module DASHI.Core.SufficientSupportFamilyInvalidationExact where

------------------------------------------------------------------------
-- Alternative sufficient derivations are not a flat dependency DAG.
-- A claim is globally invalidated only when every sufficient support route is
-- hit by a broken assumption.  One surviving sufficient route constructively
-- refutes global invalidation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true)

record SufficientSupportFamily
    (Assumption : Set)
    (Holds : Assumption → Set)
    (Claim : Set) : Set₁ where
  constructor sufficientSupportFamily
  field
    Route : Set
    Requires : Route → Assumption → Set
    routeSufficient :
      (route : Route) →
      ((assumption : Assumption) →
       Requires route assumption →
       Holds assumption) →
      Claim

open SufficientSupportFamily public

RouteHit :
  ∀ {Assumption Claim}
    {Holds : Assumption → Set} →
  (family : SufficientSupportFamily Assumption Holds Claim) →
  (Broken : Assumption → Set) →
  Route family → Set
RouteHit family Broken route =
  Σ _ (λ assumption →
    Requires family route assumption × Broken assumption)

AllSufficientRoutesHit :
  ∀ {Assumption Claim}
    {Holds : Assumption → Set} →
  (family : SufficientSupportFamily Assumption Holds Claim) →
  (Broken : Assumption → Set) → Set
AllSufficientRoutesHit family Broken =
  (route : Route family) → RouteHit family Broken route

record SurvivingSufficientRoute
    {Assumption Claim : Set}
    {Holds : Assumption → Set}
    (family : SufficientSupportFamily Assumption Holds Claim)
    (Broken : Assumption → Set) : Set₁ where
  constructor survivingSufficientRoute
  field
    route : Route family
    routeUnbroken :
      (assumption : Assumption) →
      Requires family route assumption →
      Broken assumption →
      ⊥

open SurvivingSufficientRoute public

survivingSufficientRouteRefutesGlobalInvalidation :
  ∀ {Assumption Claim}
    {Holds : Assumption → Set}
    {family : SufficientSupportFamily Assumption Holds Claim}
    {Broken : Assumption → Set} →
  SurvivingSufficientRoute family Broken →
  AllSufficientRoutesHit family Broken →
  ⊥
survivingSufficientRouteRefutesGlobalInvalidation surviving global with
  global (route surviving)
... | assumption , required , broken =
  routeUnbroken surviving assumption required broken

record SupportFamilyInvalidationBoundary : Set where
  constructor supportFamilyInvalidationBoundary
  field
    oneBrokenAssumptionNeedNotInvalidateClaim : Bool
    alternativeSufficientRoutesAreFirstClass : Bool
    globalInvalidationRequiresEverySufficientRouteHit : Bool
    survivingSufficientRouteBlocksGlobalInvalidation : Bool
    supportStructureDoesNotCreateDomainTruth : Bool

canonicalSupportFamilyInvalidationBoundary :
  SupportFamilyInvalidationBoundary
canonicalSupportFamilyInvalidationBoundary =
  supportFamilyInvalidationBoundary true true true true true
