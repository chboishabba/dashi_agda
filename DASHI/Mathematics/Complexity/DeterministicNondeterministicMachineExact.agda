module DASHI.Mathematics.Complexity.DeterministicNondeterministicMachineExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Stephen A. Cook,
-- "The complexity of theorem-proving procedures",
-- Proceedings of STOC 1971, 151--158.
-- DOI: 10.1145/800157.805047.
--
-- Michael Sipser,
-- "Introduction to the Theory of Computation", third edition.
-- No DOI is asserted for the textbook edition used here.
--
-- DASHI CONTRIBUTION
--
-- Add explicit deterministic and nondeterministic machine semantics.  A
-- deterministic transition is a partial next-configuration function; a
-- nondeterministic transition returns a finite list of successors.  Exact-step
-- reachability is inductive, and every deterministic machine embeds into the
-- nondeterministic model through singleton successor lists.
--
-- The embedding theorem proves that every deterministic run yields a
-- nondeterministic run of the same length and preserves bounded acceptance.
-- Polynomial clocks, tape encodings, universal simulation and Cook--Levin
-- tableau size remain separate obligations.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_)

record DeterministicMachine : Set₁ where
  field
    Input : Set
    Configuration : Set
    initial : Input → Configuration
    next : Configuration → Maybe Configuration
    accepting : Configuration → Set

open DeterministicMachine public

iterateDeterministic :
  (machine : DeterministicMachine) →
  Nat → Configuration machine → Maybe (Configuration machine)
iterateDeterministic machine zero configuration = just configuration
iterateDeterministic machine (suc steps) configuration with next machine configuration
... | nothing = nothing
... | just successor = iterateDeterministic machine steps successor

record DeterministicAcceptsWithin
    (machine : DeterministicMachine)
    (input : Input machine)
    (bound : Nat) : Set₁ where
  field
    steps : Nat
    withinBound : Set
    finalConfiguration : Configuration machine
    runResult :
      iterateDeterministic machine steps (initial machine input)
      ≡ just finalConfiguration
    finalAccepting : accepting machine finalConfiguration

record NondeterministicMachine : Set₁ where
  field
    Input : Set
    Configuration : Set
    initial : Input → Configuration
    successors : Configuration → List Configuration
    accepting : Configuration → Set

open NondeterministicMachine public

------------------------------------------------------------------------
-- Finite-list membership and exact-step nondeterministic reachability.
------------------------------------------------------------------------

data Member {A : Set} (value : A) : List A → Set where
  here : ∀ {values} → Member value (value ∷ values)
  there : ∀ {other values} → Member value values →
    Member value (other ∷ values)

data NDReach
    (machine : NondeterministicMachine) :
    Nat → Configuration machine → Configuration machine → Set where
  ndRefl : ∀ {configuration} →
    NDReach machine zero configuration configuration
  ndStep : ∀ {steps start middle finish} →
    Member middle (successors machine start) →
    NDReach machine steps middle finish →
    NDReach machine (suc steps) start finish

record NondeterministicAcceptsWithin
    (machine : NondeterministicMachine)
    (input : Input machine)
    (bound : Nat) : Set₁ where
  field
    steps : Nat
    withinBound : Set
    finalConfiguration : Configuration machine
    reachable :
      NDReach machine steps (initial machine input) finalConfiguration
    finalAccepting : accepting machine finalConfiguration

------------------------------------------------------------------------
-- Deterministic machine as singleton-branching nondeterministic machine.
------------------------------------------------------------------------

singletonSuccessors : ∀ {A : Set} → Maybe A → List A
singletonSuccessors nothing = []
singletonSuccessors (just value) = value ∷ []

deterministicAsNondeterministic :
  DeterministicMachine → NondeterministicMachine
deterministicAsNondeterministic machine = record
  { Input = Input machine
  ; Configuration = Configuration machine
  ; initial = initial machine
  ; successors = λ configuration →
      singletonSuccessors (next machine configuration)
  ; accepting = accepting machine
  }

deterministicRunGivesNDReach :
  ∀ machine steps start finish →
  iterateDeterministic machine steps start ≡ just finish →
  NDReach (deterministicAsNondeterministic machine) steps start finish
deterministicRunGivesNDReach machine zero start finish runResult with runResult
... | refl = ndRefl
deterministicRunGivesNDReach machine (suc steps) start finish runResult
    with next machine start
... | nothing = impossible runResult
  where
    impossible : nothing ≡ just finish →
      NDReach (deterministicAsNondeterministic machine)
        (suc steps) start finish
    impossible ()
... | just middle =
  ndStep here
    (deterministicRunGivesNDReach machine steps middle finish runResult)

boundedDeterministicAcceptanceEmbeds :
  ∀ machine input bound →
  DeterministicAcceptsWithin machine input bound →
  NondeterministicAcceptsWithin
    (deterministicAsNondeterministic machine) input bound
boundedDeterministicAcceptanceEmbeds machine input bound acceptance = record
  { NondeterministicAcceptsWithin.steps =
      DeterministicAcceptsWithin.steps acceptance
  ; NondeterministicAcceptsWithin.withinBound =
      DeterministicAcceptsWithin.withinBound acceptance
  ; NondeterministicAcceptsWithin.finalConfiguration =
      DeterministicAcceptsWithin.finalConfiguration acceptance
  ; NondeterministicAcceptsWithin.reachable =
      deterministicRunGivesNDReach machine
        (DeterministicAcceptsWithin.steps acceptance)
        (initial machine input)
        (DeterministicAcceptsWithin.finalConfiguration acceptance)
        (DeterministicAcceptsWithin.runResult acceptance)
  ; NondeterministicAcceptsWithin.finalAccepting =
      DeterministicAcceptsWithin.finalAccepting acceptance
  }

record PolynomialClockedDeterministicMachine : Setω where
  field
    machine : DeterministicMachine
    inputLength : Input machine → Nat
    clock : Nat → Nat
    clockPolynomiallyBounded : Set
    decidesLanguageWithinClock : Set

record PolynomialClockedNondeterministicMachine : Setω where
  field
    machine : NondeterministicMachine
    inputLength : Input machine → Nat
    clock : Nat → Nat
    clockPolynomiallyBounded : Set
    acceptsLanguageWithinClock : Set
    branchDescriptionPolynomiallyBounded : Set

record MachineVerifierEquivalence : Setω where
  field
    nondeterministicMachine : PolynomialClockedNondeterministicMachine
    verifierCarrier : Set
    encodeAcceptingBranchAsCertificate : Set
    decodeCertificateAsAcceptingBranch : Set
    soundness : Set
    completeness : Set
    polynomialOverhead : Set

data ComplexityMachineLayer : Set where
  extensionalLanguage
  deterministicMachineLayer
  nondeterministicMachineLayer
  verifierCertificateLayer
  cookLevinTableauLayer

machineModelIsNotCookLevinProof :
  nondeterministicMachineLayer ≡ cookLevinTableauLayer → ⊥
machineModelIsNotCookLevinProof ()
