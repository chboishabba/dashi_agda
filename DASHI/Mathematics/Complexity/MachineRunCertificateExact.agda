module DASHI.Mathematics.Complexity.MachineRunCertificateExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Stephen A. Cook,
-- "The complexity of theorem-proving procedures",
-- Proceedings of STOC 1971, 151--158.
-- DOI: 10.1145/800157.805047.
--
-- DASHI CONTRIBUTION
--
-- Replace the opaque accepting-branch/certificate fields by an exact finite
-- path representation.  A path certificate is a list of successor
-- configurations together with a local transition witness at each step.
-- Exact-step nondeterministic reachability converts to such a certificate and
-- back, preserving the path length.  Bounded acceptance therefore yields a
-- finite accepting certificate with the same bound witness.
--
-- Boolean encoding of configurations and polynomial bit-size overhead remain
-- separate machine-representation obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)
open import Data.Product using (_×_; _,_)
open import Data.Nat.Base using (_≤_)

import DASHI.Mathematics.Complexity.DeterministicNondeterministicMachineExact as Machine

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ values) = suc (listLength values)

congruenceSuc : ∀ {left right : Nat} → left ≡ right → suc left ≡ suc right
congruenceSuc refl = refl

data ValidRunPath
    (machine : Machine.NondeterministicMachine) :
    Machine.nConfiguration machine →
    List (Machine.nConfiguration machine) →
    Machine.nConfiguration machine → Set where
  pathDone : ∀ {configuration} →
    ValidRunPath machine configuration [] configuration

  pathStep : ∀ {start next finish tail} →
    Machine.Member next (Machine.nSuccessors machine start) →
    ValidRunPath machine next tail finish →
    ValidRunPath machine start (next ∷ tail) finish

record RunCertificate
    (machine : Machine.NondeterministicMachine)
    (steps : Nat)
    (start finish : Machine.nConfiguration machine) : Set where
  constructor runCertificate
  field
    path : List (Machine.nConfiguration machine)
    pathLength : listLength path ≡ steps
    validPath : ValidRunPath machine start path finish

open RunCertificate public

reachabilityToCertificate :
  ∀ {machine steps start finish} →
  Machine.NDReach machine steps start finish →
  RunCertificate machine steps start finish
reachabilityToCertificate Machine.ndRefl =
  runCertificate [] refl pathDone
reachabilityToCertificate
    (Machine.ndStep {middle = middle} membership remainingReachability)
    with reachabilityToCertificate remainingReachability
... | runCertificate path lengthProof validity =
  runCertificate
    (middle ∷ path)
    (congruenceSuc lengthProof)
    (pathStep membership validity)

certificateToReachability :
  ∀ {machine steps start finish} →
  RunCertificate machine steps start finish →
  Machine.NDReach machine steps start finish
certificateToReachability
    (runCertificate [] refl pathDone) =
  Machine.ndRefl
certificateToReachability
    (runCertificate (next ∷ path) refl (pathStep membership validity)) =
  Machine.ndStep membership
    (certificateToReachability
      (runCertificate path refl validity))

reachabilityCertificateRoundTrip :
  ∀ {machine steps start finish}
    (reachability : Machine.NDReach machine steps start finish) →
  Machine.NDReach machine steps start finish
reachabilityCertificateRoundTrip reachability =
  certificateToReachability (reachabilityToCertificate reachability)

record AcceptingRunCertificate
    (machine : Machine.NondeterministicMachine)
    (input : Machine.nInput machine)
    (bound : Nat) : Set₁ where
  constructor acceptingRunCertificate
  field
    steps : Nat
    withinBound : steps ≤ bound
    finalConfiguration : Machine.nConfiguration machine
    run : RunCertificate machine steps
      (Machine.nInitial machine input) finalConfiguration
    accepting : Machine.nAccepting machine finalConfiguration

open AcceptingRunCertificate public

boundedAcceptanceGivesFiniteCertificate :
  ∀ machine input bound →
  Machine.NondeterministicAcceptsWithin machine input bound →
  AcceptingRunCertificate machine input bound
boundedAcceptanceGivesFiniteCertificate machine input bound acceptance =
  acceptingRunCertificate
    (Machine.nSteps acceptance)
    (Machine.nWithinBound acceptance)
    (Machine.nFinalConfiguration acceptance)
    (reachabilityToCertificate (Machine.nReachable acceptance))
    (Machine.nFinalAccepting acceptance)

finiteCertificateGivesBoundedAcceptance :
  ∀ machine input bound →
  AcceptingRunCertificate machine input bound →
  Machine.NondeterministicAcceptsWithin machine input bound
finiteCertificateGivesBoundedAcceptance machine input bound certificate = record
  { Machine.NondeterministicAcceptsWithin.nSteps = steps certificate
  ; Machine.NondeterministicAcceptsWithin.nWithinBound = withinBound certificate
  ; Machine.NondeterministicAcceptsWithin.nFinalConfiguration =
      finalConfiguration certificate
  ; Machine.NondeterministicAcceptsWithin.nReachable =
      certificateToReachability (run certificate)
  ; Machine.NondeterministicAcceptsWithin.nFinalAccepting = accepting certificate
  }

record BranchEncodingPolynomialBoundary
    (machine : Machine.NondeterministicMachine) : Set₁ where
  field
    BitString : Set
    encodeConfiguration : Machine.nConfiguration machine → BitString
    encodePath : List (Machine.nConfiguration machine) → BitString
    decodePath : BitString → List (Machine.nConfiguration machine)
    decodingCorrectOnEncodedPaths : Set
    encodedConfigurationLengthBound : Set
    encodedPathLengthPolynomialInStepsAndInput : Set
    localTransitionCheckPolynomial : Set
