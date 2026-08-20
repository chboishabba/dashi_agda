module DASHI.Governance.DomainIndexedPeaceSubjectCarrier where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Domain-indexed peace / subject-carrier distinction.
--
-- Peace, de-escalation and coercion are indexed by policy domain.  A policy
-- stance in one domain has no automatic promotion to another domain.  This is
-- a formal carrier for comparative analysis, not an empirical judgement about
-- any named government or actor.
------------------------------------------------------------------------

record DomainIndexedPolicy : Set₁ where
  field
    Actor : Set
    Domain : Set
    Action : Set
    policy : Actor → Domain → Action
    Deescalatory : Domain → Action → Set
    Coercive : Domain → Action → Set

open DomainIndexedPolicy public

record PeaceAt
    (P : DomainIndexedPolicy)
    (actor : Actor P)
    (domain : Domain P) : Set where
  field
    deescalatory : Deescalatory P domain (policy P actor domain)

open PeaceAt public

-- No unindexed `Peaceful actor` constructor is manufactured from one domain.
data DomainPeaceAutomaticallyGlobal
    {P : DomainIndexedPolicy}
    {actor : Actor P}
    {domain : Domain P}
    (p : PeaceAt P actor domain) : Set where

domainPeaceDoesNotAutomaticallyGlobalise :
  ∀ {P actor domain} {p : PeaceAt P actor domain} →
  DomainPeaceAutomaticallyGlobal p → ⊥
domainPeaceDoesNotAutomaticallyGlobalise ()

------------------------------------------------------------------------
-- Negotiating subject versus threat carrier.
------------------------------------------------------------------------

data PolicyStanding : Set where
  negotiatingSubject threatCarrier : PolicyStanding

record StandingSystem : Set₁ where
  field
    Actor : Set
    Evidence : Set
    standing : Actor → PolicyStanding
    Claims : Actor → Set
    considersClaim : (actor : Actor) → Claims actor → Set
    classifyStanding : Actor → Evidence → PolicyStanding

open StandingSystem public

record SubjectToCarrierConversion (S : StandingSystem) : Set₁ where
  field
    actor : Actor S
    evidence : Evidence S
    beforeIsSubject : standing S actor ≡ negotiatingSubject
    afterIsCarrier : classifyStanding S actor evidence ≡ threatCarrier

open SubjectToCarrierConversion public

record CarrierToSubjectReopening (S : StandingSystem) : Set₁ where
  field
    actor : Actor S
    evidence : Evidence S
    reopened : classifyStanding S actor evidence ≡ negotiatingSubject

open CarrierToSubjectReopening public

------------------------------------------------------------------------
-- Two action fibres may be glued into one public identity while remaining
-- semantically distinct.  This prevents a universal moral predicate from being
-- silently inferred from a domain-specific projection.
------------------------------------------------------------------------

record TwoDomainPolicyFibre (P : DomainIndexedPolicy) : Set₁ where
  field
    first second : Domain P
    PublicIdentity : Set
    glue : Action P → Action P → PublicIdentity

open TwoDomainPolicyFibre public

record MixedDomainWitness
    {P : DomainIndexedPolicy}
    (F : TwoDomainPolicyFibre P)
    (actor : Actor P) : Set₁ where
  field
    firstDeescalatory : Deescalatory P (first F) (policy P actor (first F))
    secondCoercive : Coercive P (second F) (policy P actor (second F))

open MixedDomainWitness public

------------------------------------------------------------------------
-- Source boundary for the motivating contemporary phrase.
--
-- "Peace Through Strength" is used in official US executive communications.
-- Government/web communications have no scholarly DOI; they motivate the
-- domain-indexed example but provide no proof authority for the generic model.
------------------------------------------------------------------------

data DomainIndexedPolicyIsUniversalMoralDiagnosis : Set where

domainIndexedPolicyDoesNotDiagnoseMorality :
  DomainIndexedPolicyIsUniversalMoralDiagnosis → ⊥
domainIndexedPolicyDoesNotDiagnoseMorality ()
