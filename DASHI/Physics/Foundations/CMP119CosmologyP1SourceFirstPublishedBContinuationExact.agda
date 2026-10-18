{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP1SourceFirstPublishedBContinuationExact where

------------------------------------------------------------------------
-- S1 SOURCE-FIRST MAX-CUT.
--
-- `CMP109116LiteralEffectiveActionContinuation` leaves its Background and
-- Tangent carriers abstract.  Therefore a later equality
--
--   repository Background = published CMP119 B-coordinate
--
-- and ten later tangent identifications are avoidable representation debt.
-- Construct the continuation directly on the published B carrier and choose the
-- tangent carrier to be the canonical ten-slot symmetric metric/source carrier.
--
-- This does NOT manufacture the source continuation theorem.  The remaining
-- physical/source content is exactly the literal CMP109 potential, CMP116
-- substituted local activities, and their source-published finite-sum identity
-- on this B carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source

record SourceFirstPublishedBContinuation
    (Scale Volume PublishedB Component : Set) : Set₁ where
  field
    components : Scale → Volume → List Component

    cmp116PhysicalLocalizedActivity :
      Scale → Volume → Component → PublishedB → ℝ

    cmp109EffectivePotential :
      Scale → Volume → PublishedB → ℝ

    effectivePotentialIsLocalizedCompositeSum :
      ∀ scale volume background →
      cmp109EffectivePotential scale volume background
      ≡ Finite.sumFunctions
          (Finite.mapList
            (cmp116PhysicalLocalizedActivity scale volume)
            (components scale volume))
          background

open SourceFirstPublishedBContinuation public

asLiteralCMP109116Continuation :
  ∀ {Scale Volume PublishedB Component} →
  SourceFirstPublishedBContinuation Scale Volume PublishedB Component →
  Source.CMP109116LiteralEffectiveActionContinuation
asLiteralCMP109116Continuation data = record
  { Source.CMP109116LiteralEffectiveActionContinuation.Scale = Scale
  ; Source.CMP109116LiteralEffectiveActionContinuation.Volume = Volume
  ; Source.CMP109116LiteralEffectiveActionContinuation.Background = PublishedB
  ; Source.CMP109116LiteralEffectiveActionContinuation.Tangent =
      K.SymmetricTensorComponent4
  ; Source.CMP109116LiteralEffectiveActionContinuation.Component = Component
  ; Source.CMP109116LiteralEffectiveActionContinuation.components =
      components data
  ; Source.CMP109116LiteralEffectiveActionContinuation.cmp116PhysicalLocalizedActivity =
      cmp116PhysicalLocalizedActivity data
  ; Source.CMP109116LiteralEffectiveActionContinuation.cmp109EffectivePotential =
      cmp109EffectivePotential data
  ; Source.CMP109116LiteralEffectiveActionContinuation.effectivePotentialIsLocalizedCompositeSum =
      effectivePotentialIsLocalizedCompositeSum data
  }
  where
    Scale = _
    Volume = _
    PublishedB = _
    Component = _

-- Explicit projections make the same-object facts reducible, rather than
-- external source hypotheses.
backgroundCarrierIsPublishedBByConstruction :
  ∀ {Scale Volume PublishedB Component}
    (data : SourceFirstPublishedBContinuation Scale Volume PublishedB Component) →
  Source.Background (asLiteralCMP109116Continuation data) ≡ PublishedB
backgroundCarrierIsPublishedBByConstruction data = Agda.Builtin.Equality.refl

tangentCarrierIsCanonicalTenSlotByConstruction :
  ∀ {Scale Volume PublishedB Component}
    (data : SourceFirstPublishedBContinuation Scale Volume PublishedB Component) →
  Source.Tangent (asLiteralCMP109116Continuation data)
  ≡ K.SymmetricTensorComponent4
tangentCarrierIsCanonicalTenSlotByConstruction data = Agda.Builtin.Equality.refl

postHocBackgroundCarrierEqualityRequired : Bool
postHocBackgroundCarrierEqualityRequired = false

postHocTenTangentIdentificationsRequired : Bool
postHocTenTangentIdentificationsRequired = false

remainingS1WorkIsLiteralContinuationOnPublishedBCarrier : Bool
remainingS1WorkIsLiteralContinuationOnPublishedBCarrier = true
