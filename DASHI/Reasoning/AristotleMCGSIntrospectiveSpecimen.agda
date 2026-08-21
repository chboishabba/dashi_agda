module DASHI.Reasoning.AristotleMCGSIntrospectiveSpecimen where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.AristotleMCGSHypergraphExact as Aristotle

open Aristotle using
  ( SearchHypergraph
  ; StateProved
  ; ActionProved
  ; StateObserver
  ; byAction
  ; allTargets
  ; all[]
  ; _all∷_
  )

------------------------------------------------------------------------
-- Finite introspective specimen.
--
-- The specimen deliberately contains:
--   * an OR root S0 with two successful actions and one failed action;
--   * an AND action A0 whose two children must both close;
--   * terminal successful actions T1/T1p/T2/T3;
--   * a dead state S4 and therefore failed action A2;
--   * two distinct fine states S1 and S1p in the same observer fibre.
--
-- This is the source object rendered by
-- scripts/aristotle_introspective_roundtrip.py.
------------------------------------------------------------------------

data State : Set where
  S0 S1 S1p S2 S3 S4 : State

data Action : Set where
  A0 A1 A2 T1 T1p T2 T3 : Action

source : Action → State
source A0  = S0
source A1  = S0
source A2  = S0
source T1  = S1
source T1p = S1p
source T2  = S2
source T3  = S3

targets : Action → List State
targets A0  = S1 ∷ S2 ∷ []
targets A1  = S3 ∷ []
targets A2  = S4 ∷ []
targets T1  = []
targets T1p = []
targets T2  = []
targets T3  = []

specimenGraph : SearchHypergraph
specimenGraph = record
  { State = State
  ; Action = Action
  ; source = source
  ; targets = targets
  }

------------------------------------------------------------------------
-- Exact AND/OR proof certificates.
------------------------------------------------------------------------

s1Proved : StateProved specimenGraph S1
s1Proved = byAction T1 refl (allTargets all[])

s1pProved : StateProved specimenGraph S1p
s1pProved = byAction T1p refl (allTargets all[])

s2Proved : StateProved specimenGraph S2
s2Proved = byAction T2 refl (allTargets all[])

s3Proved : StateProved specimenGraph S3
s3Proved = byAction T3 refl (allTargets all[])

a0Proved : ActionProved specimenGraph A0
a0Proved = allTargets (s1Proved all∷ s2Proved all∷ all[])

a1Proved : ActionProved specimenGraph A1
a1Proved = allTargets (s3Proved all∷ all[])

s0ProvedViaA0 : StateProved specimenGraph S0
s0ProvedViaA0 = byAction A0 refl a0Proved

------------------------------------------------------------------------
-- The deliberately dead branch really is dead.
------------------------------------------------------------------------

data ⊥ : Set where

s4Unproved : StateProved specimenGraph S4 → ⊥
s4Unproved (byAction A0  () actionProof)
s4Unproved (byAction A1  () actionProof)
s4Unproved (byAction A2  () actionProof)
s4Unproved (byAction T1  () actionProof)
s4Unproved (byAction T1p () actionProof)
s4Unproved (byAction T2  () actionProof)
s4Unproved (byAction T3  () actionProof)

a2Unproved : ActionProved specimenGraph A2 → ⊥
a2Unproved (allTargets (s4 all∷ all[])) = s4Unproved s4

------------------------------------------------------------------------
-- Observer quotient: S1 and S1p are distinct fine states but one surface.
------------------------------------------------------------------------

data Observable : Set where
  Q0 Q1 Q2 Q3 Q4 : Observable

observe : State → Observable
observe S0  = Q0
observe S1  = Q1
observe S1p = Q1
observe S2  = Q2
observe S3  = Q3
observe S4  = Q4

specimenObserver : StateObserver specimenGraph
specimenObserver = record
  { Observable = Observable
  ; observe = observe
  }

s1AndS1pObserverEquivalent :
  Aristotle._≈[_]_ S1 specimenObserver S1p
s1AndS1pObserverEquivalent = refl

------------------------------------------------------------------------
-- Declared visual signature.  These functions are the source-side values
-- compared pointwise against the OpenCV-recovered values in the witness file.
------------------------------------------------------------------------

expectedStateProved : State → Bool
expectedStateProved S0  = true
expectedStateProved S1  = true
expectedStateProved S1p = true
expectedStateProved S2  = true
expectedStateProved S3  = true
expectedStateProved S4  = false

expectedActionProved : Action → Bool
expectedActionProved A0  = true
expectedActionProved A1  = true
expectedActionProved A2  = false
expectedActionProved T1  = true
expectedActionProved T1p = true
expectedActionProved T2  = true
expectedActionProved T3  = true

-- Undirected visual incidence: a state and action are connected whenever the
-- state is the action source or one of its targets.
expectedIncident : State → Action → Bool
expectedIncident S0  A0  = true
expectedIncident S0  A1  = true
expectedIncident S0  A2  = true
expectedIncident S1  A0  = true
expectedIncident S1  T1  = true
expectedIncident S1p T1p = true
expectedIncident S2  A0  = true
expectedIncident S2  T2  = true
expectedIncident S3  A1  = true
expectedIncident S3  T3  = true
expectedIncident S4  A2  = true
expectedIncident _   _   = false

expectedSharedFibreTag : State → Bool
expectedSharedFibreTag S1  = true
expectedSharedFibreTag S1p = true
expectedSharedFibreTag _   = false

specimenReading : String
specimenReading =
  "Aristotle introspective specimen: AND/OR hypergraph, failed branch, and a nontrivial observer fibre."
