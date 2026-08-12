module DASHI.Core.PropositionLocalRelationTransport where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Proposition-local relational composition.
--
-- Connectivity in a provenance graph does not inherit arbitrary propositions.
-- A two-edge path may support a downstream proposition only when the concrete
-- relation pair and proposition carry an explicit transport licence.
--
-- This is deliberately generic.  Kinship, nationality, social association,
-- co-attendance, political membership, documentary mention, and historical
-- descent are not granted culpability/knowledge transport merely because they
-- are graph edges.
------------------------------------------------------------------------

record TypedRelationSystem : Set₁ where
  field
    Node : Set
    Relation : Set
    Proposition : Set
    Evidence : Set
    Provenance : Set

    Edge : Relation → Node → Node → Set
    supports : Evidence → Proposition → Set
    provenanceOf : Evidence → Provenance

open TypedRelationSystem public

record TwoStepPath
    (G : TypedRelationSystem)
    (source middle target : Node G)
    (first second : Relation G) : Set where
  constructor twoStepPath
  field
    firstEdge : Edge G first source middle
    secondEdge : Edge G second middle target

open TwoStepPath public

record TransportLicence
    (G : TypedRelationSystem)
    (first second : Relation G)
    (proposition : Proposition G) : Set₁ where
  constructor transportLicence
  field
    TransportEvidence : Set
    transportEvidence : TransportEvidence

open TransportLicence public

record LicensedPathClaim
    (G : TypedRelationSystem)
    {source middle target : Node G}
    {first second : Relation G}
    (path : TwoStepPath G source middle target first second)
    (proposition : Proposition G) : Set₁ where
  constructor licensedPathClaim
  field
    licence : TransportLicence G first second proposition
    evidence : Evidence G
    evidenceSupportsClaim : supports G evidence proposition

open LicensedPathClaim public

------------------------------------------------------------------------
-- No constructor exists from path existence alone to proposition support.
-- The empty token below makes the non-promotion boundary executable.
------------------------------------------------------------------------

data UnlicensedPathPromotion
    (G : TypedRelationSystem)
    {source middle target : Node G}
    {first second : Relation G}
    (path : TwoStepPath G source middle target first second)
    (proposition : Proposition G) : Set where

unlicensedPathPromotionImpossible :
  ∀ {G source middle target first second proposition}
    {path : TwoStepPath G source middle target first second} →
  UnlicensedPathPromotion G path proposition → ⊥
unlicensedPathPromotionImpossible ()

------------------------------------------------------------------------
-- Role-equivariant promotion schema.
--
-- Identity labels are deliberately absent.  A promotion rule consumes typed
-- evidence and a proposition.  If two actors are related by an application-
-- supplied role transport preserving evidence structure, the rule itself is
-- required to transform rather than silently changing threshold by identity.
------------------------------------------------------------------------

record PromotionRule (G : TypedRelationSystem) : Set₁ where
  field
    Decision : Set
    decide : Evidence G → Proposition G → Decision

open PromotionRule public

record RoleEquivariantPromotion
    (G : TypedRelationSystem)
    (rule : PromotionRule G) : Set₁ where
  field
    transportEvidence : Evidence G → Evidence G
    transportProposition : Proposition G → Proposition G
    transportDecision : Decision rule → Decision rule
    equivariant :
      (evidence : Evidence G) →
      (proposition : Proposition G) →
      decide rule
        (transportEvidence evidence)
        (transportProposition proposition)
      ≡ transportDecision (decide rule evidence proposition)

open RoleEquivariantPromotion public
