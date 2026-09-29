module DASHI.Mathematics.Complexity.PNotEqualsNPUniformTransitionTraceCubeNoGoExact where

------------------------------------------------------------------------
-- FIXED UNIFORM TRANSITION DOES NOT FORCE A LOW-DIMENSIONAL TRACE FAMILY
--
-- P11 surviving hope:
--
--   perhaps a single fixed program / transition schema forces its length-T
--   computation traces into a small algebraic family.
--
-- Uniformity alone does not.
--
-- This owner gives one fixed deterministic transition on a dependent finite
-- bit tape.  The machine simply emits the current head bit and advances to the
-- tail.  For every desired length-T Boolean trace, initialize the tape with
-- exactly those T bits.  The resulting T-step observation trace is definitionally
-- that desired vector.
--
-- Therefore the trace family of one fixed transition schema is the full
-- Boolean cube at every horizon.
--
-- This does NOT model SAT or a self-diagonal computation.  It proves the
-- narrower no-go needed for P11:
--
--   fixed finite program / time-homogeneous transition
--   does not by itself imply low-dimensional or low-degree trace structure.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (Σ; _,_)
open import Data.Vec.Base using (Vec; []; _∷_)

------------------------------------------------------------------------
-- One fixed state carrier and transition.
------------------------------------------------------------------------

record StreamState : Set where
  constructor streamState
  field
    remaining : Nat
    tape : Vec Bool remaining

open StreamState public

observeHead : StreamState → Bool
observeHead (streamState zero []) =
  false
observeHead (streamState (suc remaining) (bit ∷ bits)) =
  bit

advanceStream : StreamState → StreamState
advanceStream (streamState zero []) =
  streamState zero []
advanceStream (streamState (suc remaining) (bit ∷ bits)) =
  streamState remaining bits

------------------------------------------------------------------------
-- Fixed-horizon observation trace.
------------------------------------------------------------------------

observeTrace :
  (steps : Nat) →
  StreamState →
  Vec Bool steps
observeTrace zero state =
  []
observeTrace (suc steps) state =
  observeHead state
  ∷
  observeTrace steps (advanceStream state)

initialStream :
  ∀ {steps : Nat} →
  Vec Bool steps →
  StreamState
initialStream {steps} bits =
  streamState steps bits

------------------------------------------------------------------------
-- Main theorem: every Boolean trace is realized exactly.
------------------------------------------------------------------------

streamTraceExact :
  ∀ {steps : Nat}
    (desired : Vec Bool steps) →
  observeTrace
    steps
    (initialStream desired)
  ≡ desired
streamTraceExact {zero} [] =
  refl
streamTraceExact {suc steps} (bit ∷ bits)
    rewrite streamTraceExact bits =
  refl

TraceWitness :
  ∀ {steps : Nat} →
  Vec Bool steps →
  Set
TraceWitness {steps} desired =
  Σ StreamState λ state →
    observeTrace steps state
    ≡ desired

everyBooleanTraceIsRealizable :
  ∀ {steps : Nat}
    (desired : Vec Bool steps) →
  TraceWitness desired
everyBooleanTraceIsRealizable desired =
  initialStream desired
  ,
  streamTraceExact desired

------------------------------------------------------------------------
-- Research consequence.
--
-- A low-dimensional/global algebraic theorem for the SAT self-evaluation
-- family cannot follow merely from:
--
--   * one fixed finite transition program;
--   * deterministic iteration;
--   * a tiny intensional description of that program.
--
-- All of those coexist here with a full Bool^T trace family across inputs.
--
-- The remaining leverage must use something special about the self-diagonal
-- SAT semantics or impose a proved transformed/global consistency object whose
-- admissible family is genuinely smaller.
------------------------------------------------------------------------
