module DASHI.Core.AuthorityPromotionHierarchyExact where

------------------------------------------------------------------------
-- LAWFUL AUTHORITY PROMOTION HIERARCHY
--
-- The shared reopenable-consumer kernel already records the useful authority
-- vocabulary
--
--   computed < validated < supported < authorised < actionable.
--
-- This module supplies the missing mathematics: promotion evidence must travel
-- along declared adjacent edges (or their transitive closure).  An arbitrary
-- record saying `fromLevel = computed; toLevel = actionable` is not itself a
-- proof that every intervening authority obligation was discharged.
--
-- This is an internal DASHI ordering theorem.  The literature on reject/selective
-- decisions calibrates why authority must remain separate from computation, but
-- no external source is used as proof of this project-specific hierarchy.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Core.ReopenableConsumerInterventionKernelExact as Kernel

------------------------------------------------------------------------
-- Only adjacent promotions are primitive.
------------------------------------------------------------------------

data DirectPromotion :
  Kernel.AuthorityLevel → Kernel.AuthorityLevel → Set where
  computedToValidated :
    DirectPromotion Kernel.computed Kernel.validated
  validatedToSupported :
    DirectPromotion Kernel.validated Kernel.supported
  supportedToAuthorised :
    DirectPromotion Kernel.supported Kernel.authorised
  authorisedToActionable :
    DirectPromotion Kernel.authorised Kernel.actionable

------------------------------------------------------------------------
-- Reflexive-transitive closure gives the only generic multi-step route.
------------------------------------------------------------------------

data PromotionPath :
  Kernel.AuthorityLevel → Kernel.AuthorityLevel → Set where
  stay :
    ∀ {level} → PromotionPath level level
  advance :
    ∀ {from middle to} →
    DirectPromotion from middle →
    PromotionPath middle to →
    PromotionPath from to

composePromotionPath :
  ∀ {from middle to} →
  PromotionPath from middle →
  PromotionPath middle to →
  PromotionPath from to
composePromotionPath stay right = right
composePromotionPath (advance edge rest) right =
  advance edge (composePromotionPath rest right)

computedToActionablePath :
  PromotionPath Kernel.computed Kernel.actionable
computedToActionablePath =
  advance computedToValidated
    (advance validatedToSupported
      (advance supportedToAuthorised
        (advance authorisedToActionable stay)))

------------------------------------------------------------------------
-- Scoped evidence is attached to each direct edge.  This prevents one body of
-- evidence from silently being treated as validation, support, authorisation
-- and action permission at once.
------------------------------------------------------------------------

record EdgePromotionWitness
    {Carrier : Set}
    (item : Carrier)
    {from to : Kernel.AuthorityLevel}
    (edge : DirectPromotion from to) : Set₁ where
  constructor edgePromotionWitness
  field
    policyReference : Agda.Builtin.String.String
    evidenceReferences : Agda.Builtin.List.List Agda.Builtin.String.String
    authorityReference : Agda.Builtin.String.String
    scope : Agda.Builtin.String.String

open EdgePromotionWitness public

------------------------------------------------------------------------
-- A proof-carrying promotion chain mirrors the mathematical path exactly.
------------------------------------------------------------------------

data PromotionEvidenceChain
    {Carrier : Set}
    (item : Carrier) :
    ∀ {from to} → PromotionPath from to → Set₁ where
  evidenceStay :
    ∀ {level} → PromotionEvidenceChain item (stay {level})
  evidenceAdvance :
    ∀ {from middle to}
      {edge : DirectPromotion from middle}
      {rest : PromotionPath middle to} →
    EdgePromotionWitness item edge →
    PromotionEvidenceChain item rest →
    PromotionEvidenceChain item (advance edge rest)

------------------------------------------------------------------------
-- The shared generic PromotionWitness can be exported only after a lawful path
-- has been supplied.  It remains a summary; the chain is the proof object.
------------------------------------------------------------------------

record LawfulPromotion
    {Carrier : Set}
    (item : Carrier)
    (from to : Kernel.AuthorityLevel) : Set₁ where
  constructor lawfulPromotion
  field
    path : PromotionPath from to
    evidence : PromotionEvidenceChain item path

open LawfulPromotion public

lawfulPromotionComposes :
  ∀ {Carrier : Set}
    {item : Carrier}
    {from middle to : Kernel.AuthorityLevel} →
  LawfulPromotion item from middle →
  LawfulPromotion item middle to →
  PromotionPath from to
lawfulPromotionComposes left right =
  composePromotionPath (path left) (path right)

------------------------------------------------------------------------
-- Exact negative boundary: there is no primitive backwards or skipping edge.
-- The only way to inhabit PromotionPath is `stay` or repeated adjacent advance.
------------------------------------------------------------------------
