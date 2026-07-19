module DASHI.Geometry.WetsuitSeamOptimisationBoundary where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.Nat using (Nat; zero; suc; _+_; _*_; _≤_)

-- This module formalises the optimisation surface only.  It does not claim that
-- the priors below are universal biomechanical laws or that the resulting
-- candidate is a physically certified wetsuit pattern.

data BodyZone : Set where
  shoulderApex    : BodyZone
  underarmSide    : BodyZone
  spineCentre     : BodyZone
  spineAdjacent   : BodyZone
  ribSide         : BodyZone
  hipCrease       : BodyZone
  innerLeg        : BodyZone
  jointCrease     : BodyZone
  unclassified    : BodyZone

-- Design priors are explicit data, not promoted physical theorems.
preferredZone : BodyZone → Bool
preferredZone shoulderApex  = false
preferredZone underarmSide  = true
preferredZone spineCentre   = false
preferredZone spineAdjacent = true
preferredZone ribSide       = true
preferredZone hipCrease     = false
preferredZone innerLeg      = true
preferredZone jointCrease   = false
preferredZone unclassified  = false

forbiddenZone : BodyZone → Bool
forbiddenZone shoulderApex  = true
forbiddenZone underarmSide  = false
forbiddenZone spineCentre   = true
forbiddenZone spineAdjacent = false
forbiddenZone ribSide       = false
forbiddenZone hipCrease     = false
forbiddenZone innerLeg      = false
forbiddenZone jointCrease   = true
forbiddenZone unclassified  = false

record PanelBudgets : Set where
  constructor panelBudgets
  field
    maxCurvatureLoad : Nat
    maxTurningLoad   : Nat
    minFeatureSize   : Nat
    maxSeamMismatch  : Nat

open PanelBudgets public

record SeamObservation : Set where
  constructor seamObservation
  field
    curvatureLoad : Nat
    turningLoad   : Nat
    featureSize   : Nat
    seamMismatch  : Nat
    crossShear    : Nat
    bendingLoad   : Nat
    leakRisk      : Nat
    visibilityCost : Nat

open SeamObservation public

-- A panel is accepted only when all currently modelled manufacturability
-- obligations are supplied.  The record deliberately carries evidence rather
-- than computing authority from an unvalidated mesh.
record Manufacturable
  (budgets : PanelBudgets)
  (observation : SeamObservation) : Set where
  constructor manufacturable
  field
    curvatureWithinBudget : curvatureLoad observation ≤ maxCurvatureLoad budgets
    turningWithinBudget   : turningLoad observation ≤ maxTurningLoad budgets
    featureAboveMinimum   : minFeatureSize budgets ≤ featureSize observation
    seamWithinTolerance   : seamMismatch observation ≤ maxSeamMismatch budgets

open Manufacturable public

record SeamWeights : Set where
  constructor seamWeights
  field
    shearWeight      : Nat
    bendingWeight    : Nat
    leakWeight       : Nat
    visibilityWeight : Nat
    panelCountWeight : Nat

open SeamWeights public

record SeamCandidate : Set where
  constructor seamCandidate
  field
    candidateZone        : BodyZone
    candidateObservation : SeamObservation
    candidatePanelCount  : Nat

open SeamCandidate public

weightedSeamCost : SeamWeights → SeamCandidate → Nat
weightedSeamCost weights candidate =
    shearWeight weights * crossShear observation
  + bendingWeight weights * bendingLoad observation
  + leakWeight weights * leakRisk observation
  + visibilityWeight weights * visibilityCost observation
  + panelCountWeight weights * candidatePanelCount candidate
  where
    observation = candidateObservation candidate

record AdmissibleCandidate
  (budgets : PanelBudgets)
  (candidate : SeamCandidate) : Set where
  constructor admissibleCandidate
  field
    manufacturabilityWitness :
      Manufacturable budgets (candidateObservation candidate)
    forbiddenZoneAvoided : forbiddenZone (candidateZone candidate) ≡ false

open AdmissibleCandidate public

-- Optimality is relative to an explicitly supplied admissible candidate class.
-- This avoids claiming a global optimum over unmodelled bodies, motions,
-- materials, seam constructions, or manufacturing processes.
record OptimalAmongAdmissible
  (budgets : PanelBudgets)
  (weights : SeamWeights)
  (CandidateClass : SeamCandidate → Set)
  (chosen : SeamCandidate) : Set₁ where
  constructor optimalAmongAdmissible
  field
    chosenInClass : CandidateClass chosen
    chosenAdmissible : AdmissibleCandidate budgets chosen
    noWorseThanAnyAdmissible :
      (other : SeamCandidate) →
      CandidateClass other →
      AdmissibleCandidate budgets other →
      weightedSeamCost weights chosen ≤ weightedSeamCost weights other

open OptimalAmongAdmissible public

data GateResult
  (budgets : PanelBudgets)
  (observation : SeamObservation) : Set where
  accept : Manufacturable budgets observation → GateResult budgets observation
  review : GateResult budgets observation
  reject : GateResult budgets observation

acceptedEvidence :
  ∀ {budgets observation} →
  GateResult budgets observation →
  Maybe (Manufacturable budgets observation)
acceptedEvidence (accept witness) = just witness
acceptedEvidence review = nothing
acceptedEvidence reject = nothing

data SplitMode : Set where
  noSplit              : SplitMode
  singleCut            : SplitMode
  seamAwareSingleCut   : SplitMode
  multiCut             : SplitMode

record SplitAdvice : Set where
  constructor splitAdvice
  field
    splitMode             : SplitMode
    triggerBoundaryIndex  : Nat
    preservesSeamRanges   : Bool
    childIssuesRecomputed : Bool

open SplitAdvice public

-- Current repository status: a typed optimisation boundary and obligation
-- carrier, not a continuum mechanics proof or manufacturing authority.
continuumWetsuitOptimalityPromoted : Bool
continuumWetsuitOptimalityPromoted = false

automaticManufacturingAuthorityPromoted : Bool
automaticManufacturingAuthorityPromoted = false
