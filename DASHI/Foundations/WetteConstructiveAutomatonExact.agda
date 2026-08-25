module DASHI.Foundations.WetteConstructiveAutomatonExact where

------------------------------------------------------------------------
-- EDUARD WETTE SOURCE CONTEXT
--
-- Reconstruction target: Wette's constructive-arithmetic programme, especially
-- his relatively complete formal system of constructive arithmetic and the
-- later account "Vom Unendlichen zum Endlichen" (Dialectica 24, 1970).
--
-- DASHI CONTRIBUTION
--
-- Reuse the repository's KernelInternal automaton interface. Wette's exact
-- historical rule vocabulary is NOT invented here: a source reconstruction
-- must provide State, Generator, step, admissibility, and the simulation law.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Automata.KernelInternal as KI

record WetteMachineSpec : Set₁ where
  field
    State : Set
    Generator : Set
    admissible : State → Bool
    step : Generator → State → State
    preservesAdmissible :
      (g : Generator) →
      (state : State) →
      admissible state ≡ true →
      admissible (step g state) ≡ true

open WetteMachineSpec public

asKernelSystem : WetteMachineSpec → KI.KernelSystem
asKernelSystem machine =
  record
    { State = State machine
    ; Generator = Generator machine
    ; defectZero = admissible machine
    ; step = step machine
    }

asKernelInternal :
  (machine : WetteMachineSpec) →
  KI.KernelInternal (asKernelSystem machine)
asKernelInternal machine =
  record
    { preservesKernel = preservesAdmissible machine
    }

asKernelInternalAutomaton :
  WetteMachineSpec → KI.KernelInternalAutomaton
asKernelInternalAutomaton machine =
  record
    { system = asKernelSystem machine
    ; internality = asKernelInternal machine
    }

record WetteDeductionSimulation (machine : WetteMachineSpec) : Set₁ where
  field
    Syntax : Set
    encode : Syntax → State machine
    syntaxStep : Generator machine → Syntax → Syntax
    stepCommutes :
      (g : Generator machine) →
      (term : Syntax) →
      encode (syntaxStep g term) ≡ step machine g (encode term)

open WetteDeductionSimulation public

iterateSyntax :
  {machine : WetteMachineSpec} →
  (simulation : WetteDeductionSimulation machine) →
  Generator machine → Nat → Syntax simulation → Syntax simulation
iterateSyntax simulation g zero term = term
iterateSyntax simulation g (suc n) term =
  iterateSyntax simulation g n (syntaxStep simulation g term)

iterateState :
  (machine : WetteMachineSpec) →
  Generator machine → Nat → State machine → State machine
iterateState machine g zero state = state
iterateState machine g (suc n) state =
  iterateState machine g n (step machine g state)

iterate-cong :
  {machine : WetteMachineSpec} →
  (g : Generator machine) →
  (n : Nat) →
  {left right : State machine} →
  left ≡ right →
  iterateState machine g n left ≡ iterateState machine g n right
iterate-cong g n refl = refl

simulation-n-step :
  {machine : WetteMachineSpec} →
  (simulation : WetteDeductionSimulation machine) →
  (g : Generator machine) →
  (n : Nat) →
  (term : Syntax simulation) →
  encode simulation (iterateSyntax simulation g n term)
    ≡ iterateState machine g n (encode simulation term)
simulation-n-step simulation g zero term = refl
simulation-n-step {machine} simulation g (suc n) term =
  let
    one = stepCommutes simulation g term
    rest = simulation-n-step simulation g n (syntaxStep simulation g term)
  in
  trans rest (iterate-cong g n one)
  where
  trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl q = q

------------------------------------------------------------------------
-- The theorem above is deliberately conditional on stepCommutes. Recovering
-- Wette's actual calculus therefore reduces to a source-attributed finite set
-- of generator definitions plus proofs of those commuting obligations.
------------------------------------------------------------------------
