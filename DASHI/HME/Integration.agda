module DASHI.HME.Integration where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (zero)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)

open import DASHI.Physics.ClosureGlue using (ClosureAxioms)
open import DASHI.HME.Trace as Trace
open import DASHI.HME.All public
open import DASHI.HME.Generated.Witnesses public

------------------------------------------------------------------------
-- Convert canonical witness records (generated via `scripts/hme_emit_agda.py`)
-- into the typed `Trace.TraceWitness` so `WitnessBundle` can pair them with a
-- verified `Admissible` path.
------------------------------------------------------------------------

traceVectorFromCanonical : CanonicalWitness → Trace.TraceVector
traceVectorFromCanonical cw =
  record
    { id         = CanonicalWitness.traceId cw
    ; exponents  = []
    ; normalized = CanonicalWitness.residueVector cw
    ; mass       = zero
    ; sparsity   = zero
    }

traceInvariantFromCanonical : CanonicalWitness → Trace.TraceInvariant
traceInvariantFromCanonical cw =
  record
    { hotColdRatio = zero , zero
    ; basin        = CanonicalWitness.basinId cw
    ; jFixed       = false
    ; entropy      = 0.0
    ; mdlCost      = 0.0
    }

traceWitnessFromCanonical : CanonicalWitness → Trace.TraceWitness
traceWitnessFromCanonical cw =
  record
    { vector     = traceVectorFromCanonical cw
    ; invariant  = traceInvariantFromCanonical cw
    ; admissible = true
    }

--------------------------------------------------------------------------------
-- Handy accessors for the generated witness list exported by the CLI/codegen.
--------------------------------------------------------------------------------

firstTraceWitness : Maybe Trace.TraceWitness
firstTraceWitness with canonicalWitnesses
... | []      = nothing
... | cw ∷ _   = just (traceWitnessFromCanonical cw)

--------------------------------------------------------------------------------
-- Bundle helpers (tie a trace witness to an admissible path that already exists
-- in `DASHI/HME/Example.agda` via `ExampleContext`).
--------------------------------------------------------------------------------

bundleFromTrace :
  ∀ {A : ClosureAxioms} (ctx : ExampleContext) (tw : Trace.TraceWitness) →
  WitnessBundle (closure ctx) (hme ctx)
bundleFromTrace ctx tw =
  record
    { traceWitness = tw
    ; admissible   = exampleAdmissible ctx
    }
