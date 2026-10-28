module DASHI.Arithmetic.SignedSSPPrimeEmitterTraceTransportExact where

------------------------------------------------------------------------
-- REUSE / ATTRIBUTION
--
-- DASHI.Core.TypedDependencyCore owns proof-carrying admissible steps.
-- DASHI.Core.AdmissibleReachability owns their reflexive/transitive
-- closure. No competing definition of machine reachability is added.
--
-- DASHI.Arithmetic.SignedSSPPrimeOutputBoundaryExact owns the
-- ArithmeticPrimeEmitter interface; SignedSSPPrimeOffsetMacroExact
-- owns the exact power-of-two readout. Historical prime enumeration
-- by FRACTRAN belongs to Conway (1987) and Guy (1983).
--
-- NEW: a total one-step compiler that preserves the actual target
-- state after each admissible action also preserves EVERY FINITE
-- source trace. Given an independently proved source PRIMEGAME
-- completeness theorem and readout alignment, it produces a genuine
-- ArithmeticPrimeEmitter instance for the target machine.
--
-- This is a CONDITIONAL TRANSPORT: no concrete FRACDASH signed-machine
-- compiler or historical PRIMEGAME completeness proof is introduced
-- as an assumed fact. In particular the required stepAlignment below
-- must NOT be inferred from mere equality of decoded outputs.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Core.TypedDependencyCore as Dep
import DASHI.Core.AdmissibleReachability as Reach
import DASHI.Arithmetic.SignedSSPPrimeOutputBoundaryExact as Output
import DASHI.Arithmetic.SignedSSPPrimeOffsetMacroExact as Offset

-- Both action systems have the SAME typed instruction alphabet.
-- The local compiler must establish the precise next encoded state,
-- not just some target state with the same coarse observation.
record ActionTraceCompiler
    (Source Target Action : Set)
    (source : Dep.DependentActionSystem {State = Source} Action)
    (target : Dep.DependentActionSystem {State = Target} Action)
    : Set₁ where
  field
    encode : Source → Target
    stepAlignment :
      ∀ {before} →
      (action : Action) →
      (admissible : Dep.AdmissibleAction source before action) →
      Σ (Dep.AdmissibleAction target (encode before) action)
        (λ targetStep →
          Dep.after targetStep ≡ encode (Dep.after admissible))

open ActionTraceCompiler public

-- The existing Reachable owner is reused: one reflexive/inductive
-- proof transports without bounding path length in an external fuel.
traceSimulation :
  ∀ {Source Target Action : Set}
    {source : Dep.DependentActionSystem {State = Source} Action}
    {target : Dep.DependentActionSystem {State = Target} Action} →
  (compiler : ActionTraceCompiler Source Target Action source target) →
  ∀ {before after} →
  Reach.Reachable source before after →
  Reach.Reachable target (encode compiler before) (encode compiler after)
traceSimulation compiler Reach.reachableRefl = Reach.reachableRefl
traceSimulation compiler
  (Reach.reachableStep action admissible rest)
  with stepAlignment compiler action admissible
... | targetStep , targetAfterAligned =
  Reach.reachableStep action targetStep
    (subst
      (λ state → Reach.Reachable _ state _)
      (sym targetAfterAligned)
      (traceSimulation compiler rest))

-- A source PRIMEGAME may have arbitrarily many steps before an output.
-- It must supply its own sound complete emission witness for EVERY
-- arithmetic prime, rather than importing a finite regression as proof.
record ReferenceToSignedPrimeEmitter : Set₁ where
  field
    Source Target Action : Set
    sourceSystem :
      Dep.DependentActionSystem {State = Source} Action
    signedSystem :
      Dep.DependentActionSystem {State = Target} Action
    initialSource : Source
    sourceReadout : Source → Nat
    signedReadout : Target → Nat
    compiler :
      ActionTraceCompiler Source Target Action sourceSystem signedSystem
    decodedReadoutPreserved :
      (s : Source) →
      signedReadout (encode compiler s) ≡ sourceReadout s
    sourceEmitsEveryCertifiedPrime :
      (p : Nat) →
      Prime p →
      Σ Source (λ state →
        Reach.Reachable sourceSystem initialSource state
          × sourceReadout state ≡ Offset.powerTwo p)

open ReferenceToSignedPrimeEmitter public

-- This is an actual construction of the previously uninstantiated
-- output interface, conditional only on an inhabitant of the source
-- simulation/prime-generation record. The missing *concrete* instance
-- is now a named proof obligation, not a silent appeal to universality.
transportReferencePrimeEmitter :
  (bridge : ReferenceToSignedPrimeEmitter) →
  Output.ArithmeticPrimeEmitter
transportReferencePrimeEmitter bridge = record
  { State = Target bridge
  ; initial = encode (compiler bridge) (initialSource bridge)
  ; Reachable = Reach.Reachable (signedSystem bridge)
  ; readout = signedReadout bridge
  ; coversEveryPrime = λ p primeWitness →
      let example = sourceEmitsEveryCertifiedPrime bridge p primeWitness
          state = proj₁ example
          path = proj₁ (proj₂ example)
          output = proj₂ (proj₂ example)
      in
      encode (compiler bridge) state
      ,
      ( traceSimulation (compiler bridge) path
      , trans (decodedReadoutPreserved bridge state) output
      )
  }
