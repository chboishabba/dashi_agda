module DASHI.Core.FallacyPromotionBoundary where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([])
open import DASHI.Core.ArgumentObstructionCore
open import DASHI.Core.FallacyCatalogue

------------------------------------------------------------------------
-- Classification is not detection.  A detected fallacy carries both a
-- catalogue tag and an inhabited obstruction witness whose axis agrees
-- with the catalogue classification.
------------------------------------------------------------------------

record DetectedFallacy (core : ArgumentCore) : Set₁ where
  constructor detectedFallacy
  field
    kind       : FallacyKind
    obstructionWitness : Obstruction core
    axisCoherent : primaryAxis kind ≡ axis obstructionWitness

open DetectedFallacy public

record PromotionReceipt (core : ArgumentCore) (audit : AuditResult core) : Set where
  constructor promotionReceipt
  field
    noObstructions : obstructions audit ≡ []
    markedPromotable : promotable audit ≡ true

open PromotionReceipt public

cleanAuditPromotes :
  {core : ArgumentCore} →
  (a : ArgumentWitness core) →
  PromotionReceipt core (noDetectedObstruction a)
cleanAuditPromotes a = promotionReceipt refl refl

record FallacyAuditBundle (core : ArgumentCore) : Set₁ where
  constructor fallacyAuditBundle
  field
    audit    : AuditResult core
    detected : DetectedFallacy core → Set

open FallacyAuditBundle public

------------------------------------------------------------------------
-- Governance boundary:
--
-- * a catalogue name alone never blocks promotion;
-- * an inhabited obstruction may block the attempted inference route;
-- * blocking that route does not construct negation of the conclusion;
-- * promotion requires an explicit clean-audit receipt.
------------------------------------------------------------------------

catalogueNameIsNotDetection : FallacyKind → FallacyAxis
catalogueNameIsNotDetection = primaryAxis

blockedRouteLeavesConclusionOpen :
  {core : ArgumentCore} →
  DetectedFallacy core →
  Agda.Builtin.Bool.Bool
blockedRouteLeavesConclusionOpen d =
  conclusionMayStillBeTrue (obstructionWitness d)
