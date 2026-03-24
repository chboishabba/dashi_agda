module DASHI.HME.Import where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Sigma using (_,_)
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Float using (Float)
open import Data.List using (List)

open import DASHI.Physics.ClosureGlue using (ClosureAxioms; T)
open import DASHI.HME.Path
open import DASHI.HME.Trace as Trace

------------------------------------------------------------------------
-- Bridge surface: pair an imported SL witness with a canonical admissible path.
-- This keeps the proof layer unchanged while allowing external pipelines to
-- hand in structured metadata alongside a verified admissible path.
------------------------------------------------------------------------

record WitnessBundle (A : ClosureAxioms) (ctx : CanonicalContext A) : Set₁ where
  field
    traceWitness : Trace.TraceWitness
    admissible   : Admissible A ctx

open WitnessBundle public

------------------------------------------------------------------------
-- Minimal feedback surface back to SL (typed, no computation here).
------------------------------------------------------------------------

record ProofFeedback : Set₁ where
  field
    status             : Bool
    violatedConstraints : List String
    derivedInvariants   : List (String × Float)
