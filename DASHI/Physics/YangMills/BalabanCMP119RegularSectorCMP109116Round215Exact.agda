{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119RegularSectorCMP109116Round215Exact where

------------------------------------------------------------------------
-- ROUND215 / USE THE LITERAL CMP119 REGULAR E_k SECTOR FOR CMP109/CMP116
--
-- SOURCE-SCOPE CORRECTION
--
-- CMP119 Sect.2 (2.23) decomposes the complete action into a Wilson part,
-- regular small-field E_k, R-operation R_k, boundary B_k and vacuum term.
-- Immediately afterward it states that E_k has the same properties as the
-- small-field effective action constructed in CMP109 Part I, localized across
-- scales; (2.25)--(2.29) give its localized analytic pieces.
--
-- CMP109 Sect.5 Eq.(5.1) differentiates E^(j)(U_j(exp iB)); CMP116 Part II
-- continues/localizes that same fluctuation-field effective action.
-- Therefore the preferred BC1 source is the literal CMP119 E_k coordinate,
-- NOT the whole complete-density action A_k.
--
-- This module bypasses the earlier free `Density -> Potential` interpretation.
-- It builds the exact CMP109/CMP116 continuation directly from the source-native
-- `regularSmallFieldTerm` field of `CMP119Section2SourceNativeState`.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as CMP119
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Continue

record CMP119RegularSectorRealization
    {Density Background Fluctuation Action WilsonTerm SmallFieldTerm
      RTerm BoundaryTerm Vacuum : Set}
    (source : CMP119.CMP119Section2SourceNativeState
      Density Background Fluctuation Action WilsonTerm SmallFieldTerm
      RTerm BoundaryTerm Vacuum) : Set₁ where
  field
    Volume Tangent Component : Set

    -- Physical pointwise meaning of the literal regular E_k source object.
    evaluateRegularTerm : SmallFieldTerm → Background → ℝ

    components : Nat → Volume → List Component
    localizedRegularActivity :
      Nat → Volume → Component → Background → ℝ

    -- Literal CMP116 localization of the SAME E_k object.  No R/B/Wilson term
    -- may pay this equality unless it is already part of `regularSmallFieldTerm`.
    regularEIsLocalizedCompositeSum :
      ∀ scale volume background →
      evaluateRegularTerm (CMP119.regularSmallFieldTerm source scale) background
      ≡ Finite.sumFunctions
          (Finite.mapList
            (localizedRegularActivity scale volume)
            (components scale volume))
          background

open CMP119RegularSectorRealization public

asCMP109116Continuation :
  ∀ {Density Background Fluctuation Action WilsonTerm SmallFieldTerm
      RTerm BoundaryTerm Vacuum source} →
  CMP119RegularSectorRealization
    {Density} {Background} {Fluctuation} {Action} {WilsonTerm} {SmallFieldTerm}
    {RTerm} {BoundaryTerm} {Vacuum} source →
  Continue.CMP109116LiteralEffectiveActionContinuation
asCMP109116Continuation {source = source} realization = record
  { Continue.CMP109116LiteralEffectiveActionContinuation.Scale = Nat
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Volume = Volume realization
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Background =
      CMP119.Background _
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Tangent = Tangent realization
  ; Continue.CMP109116LiteralEffectiveActionContinuation.Component = Component realization
  ; Continue.CMP109116LiteralEffectiveActionContinuation.components =
      components realization
  ; Continue.CMP109116LiteralEffectiveActionContinuation.cmp116PhysicalLocalizedActivity =
      localizedRegularActivity realization
  ; Continue.CMP109116LiteralEffectiveActionContinuation.cmp109EffectivePotential =
      λ scale _ → evaluateRegularTerm realization
        (CMP119.regularSmallFieldTerm source scale)
  ; Continue.CMP109116LiteralEffectiveActionContinuation.effectivePotentialIsLocalizedCompositeSum =
      regularEIsLocalizedCompositeSum realization
  }

cmp109PotentialIsLiteralCMP119RegularE :
  ∀ {Density Background Fluctuation Action WilsonTerm SmallFieldTerm
      RTerm BoundaryTerm Vacuum source}
    (realization : CMP119RegularSectorRealization
      {Density} {Background} {Fluctuation} {Action} {WilsonTerm} {SmallFieldTerm}
      {RTerm} {BoundaryTerm} {Vacuum} source) →
  ∀ scale volume background →
  Continue.cmp109EffectivePotential (asCMP109116Continuation realization)
      scale volume background
  ≡ evaluateRegularTerm realization
      (CMP119.regularSmallFieldTerm source scale) background
cmp109PotentialIsLiteralCMP119RegularE realization scale volume background = refl

cmp119RegularSectorContinuationCompilerLevel : ProofLevel
cmp119RegularSectorContinuationCompilerLevel = machineChecked

cmp119RegularEToCMP109PotentialSameObjectLevel : ProofLevel
cmp119RegularEToCMP109PotentialSameObjectLevel = machineChecked

-- Source/physical leaf: instantiate the pointwise E_k meaning and CMP116
-- localized activities on the literal CMP119 source-native state.  The source
-- authority for the Part-I/Part-II continuation is imported elsewhere; the
-- repository same-object realization remains conditional until inhabited.
literalCMP119RegularSectorRealizationLevel : ProofLevel
literalCMP119RegularSectorRealizationLevel = conditional
