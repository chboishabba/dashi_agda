module DASHI.Arithmetic.M9MDLBraidEvaluation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

open import DASHI.Arithmetic.M9BraidPDA

------------------------------------------------------------------------
-- Endpoint/eigenposition surface.
--
-- An endpoint is a finite 3-adic address together with the ordinary carrier
-- it denotes.  The address is the native search coordinate; the Nat is only
-- the decoded witness used by arithmetic kernels.

record Endpoint : Set where
  constructor endpoint
  field
    address : Ball3
    value   : Nat
open Endpoint public

------------------------------------------------------------------------
-- Recursive factor generation and MDL selection.
--
-- Nothing here contains a list of primes.  A generator proposes candidates;
-- MDL chooses a candidate by compression gain relative to code cost.

record CandidateGenerator : Set₁ where
  field
    seed       : FactorCandidate
    next       : FactorCandidate → FactorCandidate
    candidates : List FactorCandidate
open CandidateGenerator public

record MDLScore : Set where
  constructor mdlScore
  field
    pruningGain : Nat
    codeCost    : Nat
    depthCost   : Nat
open MDLScore public

record MDLChoice (g : CandidateGenerator) : Set where
  field
    chosen      : FactorCandidate
    score       : MDLScore
    generated   : Bool
    choiceReading : String
open MDLChoice public

------------------------------------------------------------------------
-- Braid trace and survival-permissibility.

record TraceStep : Set where
  constructor traceStep
  field
    index      : Nat
    event      : Event
    stateBefore : KernelState
    stateAfter  : KernelState
    outcome     : Verdict
open TraceStep public

Trace : Set
Trace = List TraceStep

record EndpointEvaluation : Set where
  constructor endpointEvaluation
  field
    endpointWitness : Endpoint
    trace           : Trace
    firstInvalidStep : Nat
    survivedSteps    : Nat
    finalVerdict     : Verdict
open EndpointEvaluation public

-- Degree of permissibility is explicitly historical: how many braid steps
-- the endpoint survived before a nested invalidation, not Euclidean distance.
permissibilityDegree : EndpointEvaluation → Nat
permissibilityDegree = survivedSteps

------------------------------------------------------------------------
-- Braid-order comparison.

record FrontierMass : Set where
  constructor frontierMass
  field
    depth : Nat
    liveEndpoints : Nat
open FrontierMass public

record OrderedPruning : Set where
  constructor orderedPruning
  field
    first  : Event
    second : Event
    before : FrontierMass
    after  : FrontierMass
    pruned : Nat
open OrderedPruning public

record BraidMatrixEntry : Set where
  constructor braidMatrixEntry
  field
    leftThenRight : OrderedPruning
    rightThenLeft : OrderedPruning
    leftPruning   : Nat
    rightPruning  : Nat
    differs       : Bool
open BraidMatrixEntry public

-- This is the typed form of B_ij(k).  We retain both directed pruning counts
-- rather than forcing Nat subtraction to pretend it is a signed group.
BraidMatrix : Set
BraidMatrix = List BraidMatrixEntry

record NonCommutingWitness (entry : BraidMatrixEntry) : Set where
  field
    orderChangesMass : differs entry ≡ true
open NonCommutingWitness public

------------------------------------------------------------------------
-- M9 policy: maximize early pruning under hard risk bounds.

record RiskBound : Set where
  constructor riskBound
  field
    maximumPending : Nat
    deadlineWidth  : Nat
    noFalseHardFail : Bool
open RiskBound public

canonicalDelta3Risk : RiskBound
canonicalDelta3Risk = riskBound delta3 delta3 true

record M9Policy : Set₁ where
  field
    generator  : CandidateGenerator
    risk       : RiskBound
    select     : List MDLChoice generator → MDLChoice generator
    braid      : List (MDLChoice generator) → BraidWord
    policyReading : String
open M9Policy public

record M9EvaluationSurface : Set₁ where
  field
    policy       : M9Policy
    endpoints    : List Endpoint
    evaluations  : List EndpointEvaluation
    matrix       : BraidMatrix
    recursiveNotPrimeProgrammed : Bool
    deadlineIsThree : deadlineWidth (risk policy) ≡ delta3
    surfaceReading : String
open M9EvaluationSurface public
