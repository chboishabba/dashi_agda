{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109Equation51LocalizedHessianRound103Exact where

------------------------------------------------------------------------
-- ROUND103 BC1: CMP109 (5.1) -> SUM OF CMP116 PHYSICAL LOCAL HESSIANS
--
-- CMP109 Sect.5 Eq.(5.1) defines the vacuum polarization tensor as the second
-- B-variation of E^(j)(U_j(exp iB)) at B=0.  Part II localizes that same effective
-- action.  Once the literal source continuation is bound, finite derivative
-- linearity turns Eq.(5.1) into the exact localized Hessian sum consumed by B/C.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source

record CMP109Equation51OnContinuation
    (source : Source.CMP109116LiteralEffectiveActionContinuation)
    (calculus : Finite.SecondVariationLinearity
      (Source.Background source) (Source.Tangent source)) : Set₁ where
  field
    polarizationSecondVariation :
      Source.Scale source → Source.Volume source →
      Source.Background source →
      Source.Tangent source → Source.Tangent source → ℝ

    -- Literal Eq.(5.1), including the source's background coordinate and any
    -- chosen evaluation background (identity/zero-B is supplied by callers).
    equation51 : ∀ scale volume background u v →
      polarizationSecondVariation scale volume background u v
      ≡ Finite.secondVariation calculus
          (Source.cmp109EffectivePotential source scale volume)
          background u v

open CMP109Equation51OnContinuation public

asCMP109E2 :
  ∀ {source calculus}
    (eq51 : CMP109Equation51OnContinuation source calculus)
    scale volume →
  Finite.CMP109E2FromSamePotential
    (Source.atScaleVolume source scale volume) calculus
asCMP109E2 eq51 scale volume = record
  { Finite.CMP109E2FromSamePotential.cmp109E2 =
      polarizationSecondVariation eq51 scale volume
  ; Finite.CMP109E2FromSamePotential.cmp109E2IsSecondVariation =
      equation51 eq51 scale volume
  }

polarizationIsLocalizedCompositeHessianSum :
  ∀ {source calculus}
    (eq51 : CMP109Equation51OnContinuation source calculus)
    scale volume background u v →
  polarizationSecondVariation eq51 scale volume background u v
  ≡ Finite.finiteLocalizedSecondVariation
      (Source.atScaleVolume source scale volume)
      calculus background u v
polarizationIsLocalizedCompositeHessianSum {source} {calculus}
  eq51 scale volume =
  Finite.cmp109E2IsFiniteLocalizedHessian
    (Source.atScaleVolume source scale volume)
    calculus
    (asCMP109E2 eq51 scale volume)

cmp109Equation51ToLocalizedHessianCompilerLevel : ProofLevel
cmp109Equation51ToLocalizedHessianCompilerLevel = machineChecked

-- CMP109 (5.1) itself is published source authority.  The physical repository
-- seam is its exact binding to the generated finite-cutoff effective-action
-- object in `source`.
cmp109Equation51SourceLevel : ProofLevel
cmp109Equation51SourceLevel = standardImported

literalCMP109Equation51RepositoryBindingLevel : ProofLevel
literalCMP109Equation51RepositoryBindingLevel = conditional
