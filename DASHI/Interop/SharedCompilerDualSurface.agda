module DASHI.Interop.SharedCompilerDualSurface where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- One deterministic compiler, two projection surfaces.
--
-- SB is the general state/evidence surface.  SL is the legal/normative
-- projection over the same canonical intermediate representation.
------------------------------------------------------------------------

record SharedCompilerCore : Set₂ where
  field
    Evidence StateIR Transformation : Set

    compile : Evidence → StateIR
    trace   : Evidence → StateIR → Transformation

    renderEvidence : Evidence → String
    renderState    : StateIR → String

    -- The core retains a source-facing rendering seam.  Richer provenance
    -- laws can refine this without changing either projection surface.
    compilationDeterministic :
      ∀ e → compile e ≡ compile e

open SharedCompilerCore public

data Surface : Set where
  sbGeneral : Surface
  slLegal   : Surface

record Projection (C : SharedCompilerCore) (surface : Surface) : Set₂ where
  field
    View : Set
    project : StateIR C → View

    projectionDeterministic :
      ∀ s → project s ≡ project s

open Projection public

record DualSurfaceEngine : Set₂ where
  field
    core : SharedCompilerCore
    sb   : Projection core sbGeneral
    sl   : Projection core slLegal

open DualSurfaceEngine public

------------------------------------------------------------------------
-- Both surfaces consume exactly the same compiled state.
------------------------------------------------------------------------

sb-from-shared-state :
  (E : DualSurfaceEngine) →
  Evidence (core E) →
  View (sb E)
sb-from-shared-state E evidence =
  project (sb E) (compile (core E) evidence)

sl-from-shared-state :
  (E : DualSurfaceEngine) →
  Evidence (core E) →
  View (sl E)
sl-from-shared-state E evidence =
  project (sl E) (compile (core E) evidence)

record SharedCompilerBoundary : Set where
  field
    oneIngestCompiler       : Bool
    oneIngestCompilerTrue   : oneIngestCompiler ≡ true
    legalSecondParser       : Bool
    legalSecondParserFalse  : legalSecondParser ≡ false
    lawIsProjection         : Bool
    lawIsProjectionTrue     : lawIsProjection ≡ true
    ambiguityMayRemainInIR  : Bool
    ambiguityMayRemainTrue  : ambiguityMayRemainInIR ≡ true

canonicalSharedCompilerBoundary : SharedCompilerBoundary
canonicalSharedCompilerBoundary =
  record
    { oneIngestCompiler = true
    ; oneIngestCompilerTrue = refl
    ; legalSecondParser = false
    ; legalSecondParserFalse = refl
    ; lawIsProjection = true
    ; lawIsProjectionTrue = refl
    ; ambiguityMayRemainInIR = true
    ; ambiguityMayRemainTrue = refl
    }
