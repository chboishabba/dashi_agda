module DASHI.Moonshine.JInvariantFormulaicRendererRuntimeParityExact where

------------------------------------------------------------------------
-- FORMULAIC j RENDERER RUNTIME PARITY RECEIPT
--
-- This is the implementation-neutral landing surface for
-- scripts/check_j_formulaic_renderer_contract.py.  It separates:
--
--   checker implemented
--   checker observed passing
--   Agda/kernel certification
--   historical Homann RGB reproduction
--
-- so no runtime observation is promoted into a proof merely because the same
-- formulas are represented in Agda.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

checkerPath : String
checkerPath = "scripts/check_j_formulaic_renderer_contract.py"

runtimeProducerPath : String
runtimeProducerPath = "scripts/j_invariant_formulaic_raster_compare.py"

atomicEvaluatorPath : String
atomicEvaluatorPath = "scripts/cm_j_alpha_scan.py:j_invariant"

record FormulaicRendererRuntimeParityFrontier : Set where
  constructor formulaic-renderer-runtime-parity-frontier
  field
    checkerImplemented : Bool
    atomicEvaluatorReused : Bool
    standardJAnchorCheckedByRuntime : Bool
    rhoZeroAnchorCheckedByRuntime : Bool
    normalizationPhaseParityCheckedByRuntime : Bool
    visibleScaleCodeCheckedByRuntime : Bool
    pixelRoundTripCheckedByRuntime : Bool
    deterministicDiagnosticRasterCheckedByRuntime : Bool

    checkerObservedPassingOnCurrentHead : Bool
    agdaKernelCertifiedByRuntimeCheck : Bool
    historicalHomannRGBReproducedExactly : Bool

open FormulaicRendererRuntimeParityFrontier public

-- Source/static state only.  The workflow may later produce a runtime artifact;
-- this owner itself cannot manufacture that observation.
canonicalFormulaicRendererRuntimeParityFrontier :
  FormulaicRendererRuntimeParityFrontier
canonicalFormulaicRendererRuntimeParityFrontier =
  formulaic-renderer-runtime-parity-frontier
    true true true true true true true true
    false false false

runtimeCheckDoesNotKernelCertify :
  agdaKernelCertifiedByRuntimeCheck
    canonicalFormulaicRendererRuntimeParityFrontier ≡ false
runtimeCheckDoesNotKernelCertify = refl

historicalRGBStillSeparate :
  historicalHomannRGBReproducedExactly
    canonicalFormulaicRendererRuntimeParityFrontier ≡ false
historicalRGBStillSeparate = refl
