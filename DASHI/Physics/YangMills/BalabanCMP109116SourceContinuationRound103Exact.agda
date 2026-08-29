{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact where

------------------------------------------------------------------------
-- ROUND103 BC1 SOURCE CONTINUATION
-- Tadeusz Bałaban, CMP109 (1987), DOI 10.1007/BF01215223;
-- CMP116 (1988), DOI 10.1007/BF01239022.
--
-- Part II explicitly continues/localizes the fluctuation-field effective action
-- from Part I.  We choose each Part-II local activity AFTER its literal analytic
-- A=A(B) substitution, so Scale, Volume and Background are shared by type rather
-- than asserted later by opaque convention labels.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite

record CMP109116LiteralEffectiveActionContinuation : Set₁ where
  field
    Scale Volume Background Tangent Component : Set

    components : Scale → Volume → List Component

    cmp116PhysicalLocalizedActivity :
      Scale → Volume → Component → Background → ℝ

    cmp109EffectivePotential : Scale → Volume → Background → ℝ

    -- The actual evidence-bearing Part-I/Part-II same-action statement.
    effectivePotentialIsLocalizedCompositeSum :
      ∀ scale volume background →
      cmp109EffectivePotential scale volume background
      ≡ Finite.sumFunctions
          (Finite.mapList
            (cmp116PhysicalLocalizedActivity scale volume)
            (components scale volume))
          background

open CMP109116LiteralEffectiveActionContinuation public

atScaleVolume :
  (source : CMP109116LiteralEffectiveActionContinuation) →
  Scale source → Volume source → Finite.FiniteLocalizedEffectiveAction
atScaleVolume source scale volume = record
  { Finite.FiniteLocalizedEffectiveAction.Configuration = Background source
  ; Finite.FiniteLocalizedEffectiveAction.Tangent = Tangent source
  ; Finite.FiniteLocalizedEffectiveAction.Component = Component source
  ; Finite.FiniteLocalizedEffectiveAction.components = components source scale volume
  ; Finite.FiniteLocalizedEffectiveAction.localActivity =
      cmp116PhysicalLocalizedActivity source scale volume
  ; Finite.FiniteLocalizedEffectiveAction.cmp109EffectivePotential =
      cmp109EffectivePotential source scale volume
  ; Finite.FiniteLocalizedEffectiveAction.cmp109PotentialIsLocalizedSum =
      effectivePotentialIsLocalizedCompositeSum source scale volume
  }

cmp109116SourceContinuationPackagingLevel : ProofLevel
cmp109116SourceContinuationPackagingLevel = machineChecked

cmp116PartIIContinuesPartIEffectiveActionLevel : ProofLevel
cmp116PartIIContinuesPartIEffectiveActionLevel = standardImported

cmp116LocalizedCompositeActivitySourceLevel : ProofLevel
cmp116LocalizedCompositeActivitySourceLevel = standardImported

literalRepositoryCMP109116ContinuationInstantiationLevel : ProofLevel
literalRepositoryCMP109116ContinuationInstantiationLevel = conditional
