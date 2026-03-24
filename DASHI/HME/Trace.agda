module DASHI.HME.Trace where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List using (List)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- SL ↔ DA51 ↔ Agda boundary contract (types only, no semantics here).
-- These records formalize the interchange layer; computations live in
-- external pipelines (Python) and upstream canonical proofs stay intact.
------------------------------------------------------------------------

record TraceVector : Set where
  field
    id          : String
    exponents   : List Nat
    normalized  : List Float  -- S^14 projection as floats
    mass        : Nat
    sparsity    : Nat

record TraceInvariant : Set where
  field
    hotColdRatio : Nat × Nat
    basin        : Nat
    jFixed       : Bool
    entropy      : Float
    mdlCost      : Float

record TraceWitness : Set where
  field
    vector      : TraceVector
    invariant   : TraceInvariant
    admissible  : Bool

record CanonicalWitness : Set where
  field
    traceId          : String
    residueVector    : List Float
    basinId          : Nat
    invariants       : List (String × Float)
    proofSignature   : String

record ProofStatus : Set where
  field
    traceId              : String
    valid                : Bool
    violatedConstraints  : List String
    derivedInvariants    : List (String × Float)
