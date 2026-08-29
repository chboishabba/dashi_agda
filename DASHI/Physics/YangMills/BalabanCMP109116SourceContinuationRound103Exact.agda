{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact where

------------------------------------------------------------------------
-- ROUND103 BC1 SOURCE CONTINUATION
--
-- Tadeusz Bałaban,
--   Part I: Commun. Math. Phys. 109 (1987), 249--301,
--   DOI 10.1007/BF01215223.
--   Part II: Commun. Math. Phys. 116 (1988), 1--22,
--   DOI 10.1007/BF01239022.
--
-- Part II explicitly calls CMP109 "the first paper", starts from the fluctuation
-- field effective action constructed there, localizes its terms, and states that
-- the resulting exponentiated cluster expansion completes the construction of
-- the sequence of effective actions.  Sect.1 furthermore writes the local source
-- object as E(X,U,J,A) followed by the literal analytic substitutions in A.
--
-- Therefore the correct same-object carrier is the PHYSICAL COMPOSITE localized
-- activity after those substitutions, not the bare A-coordinate activity.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite

record CMP109116LiteralEffectiveActionContinuation : Set₁ where
  field
    Scale Volume Background Tangent Component : Set

    components : Scale → Volume → List Component

    -- CMP116 local term AFTER the source's A=A(B) substitution.  Its domain is
    -- the physical background coordinate differentiated in CMP109 Sect.5.
    cmp116PhysicalLocalizedActivity :
      Scale → Volume → Component → Background → ℝ

    -- The actual finite-cutoff effective action E^(j) of CMP109.
    cmp109EffectivePotential : Scale → Volume → Background → ℝ

    -- Published Part-I/Part-II same-action statement at the chosen scale/volume.
    effectivePotentialIsLocalizedCompositeSum :
      ∀ scale volume background →
      cmp109EffectivePotential scale volume background
      ≡ Finite.sumFunctions
          (Finite.mapList
            (cmp116PhysicalLocalizedActivity scale volume)
            (components scale volume))
          background

    -- Scale/volume/background conventions are literal, not merely equivalent.
    sameBlockingScaleConvention : Set
    sameFiniteVolumeConvention : Set
    sameBackgroundConfigurationConvention : Set

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

-- These source statements are directly stated by CMP116's relationship to Part I
-- and by its Sect.1 localization construction.  They are external source facts,
-- not locally promotable physical completion evidence by themselves.
cmp116PartIIContinuesPartIEffectiveActionLevel : ProofLevel
cmp116PartIIContinuesPartIEffectiveActionLevel = standardImported

cmp116LocalizedCompositeActivitySourceLevel : ProofLevel
cmp116LocalizedCompositeActivitySourceLevel = standardImported

-- Repository-level physical instantiation still requires binding the source's
-- symbols to our actual finite-cutoff generated action, scale and volume types.
literalRepositoryCMP109116ContinuationInstantiationLevel : ProofLevel
literalRepositoryCMP109116ContinuationInstantiationLevel = conditional
