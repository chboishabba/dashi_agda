module DASHI.Reasoning.RelationalPerspectiveIntegrationExact where

------------------------------------------------------------------------
-- RELATIONAL JOIN FIRST; PUSHOUT CERTIFICATION OPTIONAL
--
-- DASHI CONTRIBUTION
--
-- "Thirdness" is not definitionally a categorical colimit.  The primitive
-- object retains both embeddings, relation, residual and order trace.  A
-- stronger pushout-style universal property may be attached separately.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record RelationalJoin
    (Left Right Joined Relation Residual : Set) : Set₁ where
  field
    leftEmbed : Left → Joined
    rightEmbed : Right → Joined
    relation : Relation
    residual : Residual
    orderTrace : String
    leftRetained : Bool
    rightRetained : Bool
    notLeftOnly : Bool
    notRightOnly : Bool

open RelationalJoin public

record PushoutCertifiedRelationalJoin
    (Common Left Right Joined Relation Residual : Set)
    (commonToLeft : Common → Left)
    (commonToRight : Common → Right) : Set₁ where
  field
    baseJoin : RelationalJoin Left Right Joined Relation Residual

    commuteOnCommon :
      (c : Common) →
      leftEmbed baseJoin (commonToLeft c)
      ≡ rightEmbed baseJoin (commonToRight c)

    mediate :
      ∀ {Target : Set} →
      (leftMap : Left → Target) →
      (rightMap : Right → Target) →
      ((c : Common) →
        leftMap (commonToLeft c) ≡ rightMap (commonToRight c)) →
      Joined → Target

    mediateLeft :
      ∀ {Target : Set}
        (leftMap : Left → Target)
        (rightMap : Right → Target)
        (compat :
          (c : Common) →
          leftMap (commonToLeft c) ≡ rightMap (commonToRight c))
        (left : Left) →
      mediate leftMap rightMap compat (leftEmbed baseJoin left)
      ≡ leftMap left

    mediateRight :
      ∀ {Target : Set}
        (leftMap : Left → Target)
        (rightMap : Right → Target)
        (compat :
          (c : Common) →
          leftMap (commonToLeft c) ≡ rightMap (commonToRight c))
        (right : Right) →
      mediate leftMap rightMap compat (rightEmbed baseJoin right)
      ≡ rightMap right

    pointwiseUnique :
      ∀ {Target : Set}
        (leftMap : Left → Target)
        (rightMap : Right → Target)
        (compat :
          (c : Common) →
          leftMap (commonToLeft c) ≡ rightMap (commonToRight c))
        (candidate : Joined → Target) →
      ((left : Left) →
        candidate (leftEmbed baseJoin left) ≡ leftMap left) →
      ((right : Right) →
        candidate (rightEmbed baseJoin right) ≡ rightMap right) →
      (joined : Joined) →
      candidate joined ≡ mediate leftMap rightMap compat joined

open PushoutCertifiedRelationalJoin public

data EveryRelationalJoinIsPushout : Set where

relationalJoinDoesNotAutomaticallyPromoteToPushout :
  EveryRelationalJoinIsPushout → ⊥
relationalJoinDoesNotAutomaticallyPromoteToPushout ()

record RelationalIntegrationBoundary : Set where
  constructor relational-integration-boundary
  field
    relationEqualsSynthesis : Bool
    relationalJoinForcesHomogenisation : Bool
    everyRelationalJoinHasUniversalProperty : Bool
    pushoutCertificationMayBeAddedSeparately : Bool

canonicalRelationalIntegrationBoundary :
  RelationalIntegrationBoundary
canonicalRelationalIntegrationBoundary =
  relational-integration-boundary false false false true
