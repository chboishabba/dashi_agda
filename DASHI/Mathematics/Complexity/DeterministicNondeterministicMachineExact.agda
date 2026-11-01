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
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (_≤_)

record DeterministicMachine : Set₁ where
  field
    dInput : Set
    dConfiguration : Set
    dInitial : dInput → dConfiguration
    dNext : dConfiguration → Maybe dConfiguration
    dAccepting : dConfiguration → Set

open DeterministicMachine public

iterateDeterministic :
  (machine : DeterministicMachine) →
  Nat → dConfiguration machine → Maybe (dConfiguration machine)
iterateDeterministic machine zero configuration = just configuration
iterateDeterministic machine (suc steps) configuration
    with dNext machine configuration
... | nothing = nothing
... | just successor = iterateDeterministic machine steps successor

record DeterministicAcceptsWithin
    (machine : DeterministicMachine)
    (input : dInput machine)
    (bound : Nat) : Set₁ where
  field
    dSteps : Nat
    dWithinBound : dSteps ≤ bound
    dFinalConfiguration : dConfiguration machine
    dRunResult :
      iterateDeterministic machine dSteps (dInitial machine input)
      ≡ just dFinalConfiguration
    dFinalAccepting : dAccepting machine dFinalConfiguration

open DeterministicAcceptsWithin public

record NondeterministicMachine : Set₁ where
  field
    nInput : Set
    nConfiguration : Set
    nInitial : nInput → nConfiguration
    nSuccessors : nConfiguration → List nConfiguration
    nAccepting : nConfiguration → Set

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
    Nat → nConfiguration machine → nConfiguration machine → Set where
  ndRefl : ∀ {configuration} →
    NDReach machine zero configuration configuration
  ndStep : ∀ {steps start middle finish} →
    Member middle (nSuccessors machine start) →
    NDReach machine steps middle finish →
    NDReach machine (suc steps) start finish

record NondeterministicAcceptsWithin
    (machine : NondeterministicMachine)
    (input : nInput machine)
    (bound : Nat) : Set₁ where
  field
    nSteps : Nat
    nWithinBound : nSteps ≤ bound
    nFinalConfiguration : nConfiguration machine
    nReachable :
      NDReach machine nSteps (nInitial machine input) nFinalConfiguration
    nFinalAccepting : nAccepting machine nFinalConfiguration

open NondeterministicAcceptsWithin public

------------------------------------------------------------------------
-- Deterministic machine as singleton-branching nondeterministic machine.
------------------------------------------------------------------------

singletonSuccessors : ∀ {A : Set} → Maybe A → List A
singletonSuccessors nothing = []
singletonSuccessors (just value) = value ∷ []

deterministicAsNondeterministic :
  DeterministicMachine → NondeterministicMachine
deterministicAsNondeterministic machine = record
  { nInput = dInput machine
  ; nConfiguration = dConfiguration machine
  ; nInitial = dInitial machine
  ; nSuccessors = λ configuration →
      singletonSuccessors (dNext machine configuration)
  ; nAccepting = dAccepting machine
  }

deterministicRunGivesNDReach :
  ∀ machine steps start finish →
  iterateDeterministic machine steps start ≡ just finish →
  NDReach (deterministicAsNondeterministic machine) steps start finish
deterministicRunGivesNDReach machine zero start finish runResult with runResult
... | refl = ndRefl
deterministicRunGivesNDReach machine (suc steps) start finish runResult
    with dNext machine start
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
  { nSteps = dSteps acceptance
  ; nWithinBound = dWithinBound acceptance
  ; nFinalConfiguration = dFinalConfiguration acceptance
  ; nReachable =
      deterministicRunGivesNDReach machine
        (dSteps acceptance)
        (dInitial machine input)
        (dFinalConfiguration acceptance)
        (dRunResult acceptance)
  ; nFinalAccepting = dFinalAccepting acceptance
  }

record PolynomialClockedDeterministicMachine : Setω where
  field
    dMachine : DeterministicMachine
    dInputLength : dInput dMachine → Nat
    dClock : Nat → Nat
    dClockPolynomiallyBounded : Set
    dDecidesLanguageWithinClock : Set

record PolynomialClockedNondeterministicMachine : Setω where
  field
    nMachine : NondeterministicMachine
    nInputLength : nInput nMachine → Nat
    nClock : Nat → Nat
    nClockPolynomiallyBounded : Set
    nAcceptsLanguageWithinClock : Set
    nBranchDescriptionPolynomiallyBounded : Set

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
