module DASHI.Physics.Closure.NSTriadKNPhysicalStage3Allocation where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalScaleTrichotomy as Scale

------------------------------------------------------------------------
-- A lattice triad and a phase/polarisation-resolved state are distinct.
------------------------------------------------------------------------

record TriadStateCarrier : Set₁ where
  constructor triad-state-carrier
  field
    Polarisation Phase Amplitude : Set
    TransverseAt : Z3.FourierMode → Polarisation → Set
    RealityCompatible :
      Physical.PhysicalTriadIncidence →
      Polarisation → Polarisation → Polarisation →
      Phase → Phase → Phase → Set

open TriadStateCarrier public

record PhysicalTriadState
    (carrier : TriadStateCarrier)
    (N : Nat) : Set where
  constructor physical-triad-state
  field
    incidence : Physical.PhysicalTriadIncidence
    bounded : Physical.PhysicalTriadInCutoff N incidence

    pPolarisation qPolarisation kPolarisation :
      Polarisation carrier
    pTransverse :
      TransverseAt carrier (Physical.p incidence) pPolarisation
    qTransverse :
      TransverseAt carrier (Physical.q incidence) qPolarisation
    kTransverse :
      TransverseAt carrier (Physical.k incidence) kPolarisation

    pAmplitude qAmplitude kAmplitude : Amplitude carrier
    pPhase qPhase kPhase : Phase carrier

    realityCompatible :
      RealityCompatible carrier incidence
        pPolarisation qPolarisation kPolarisation
        pPhase qPhase kPhase

open PhysicalTriadState public

record RetainedStatePolicy
    (carrier : TriadStateCarrier)
    (N : Nat) : Set₁ where
  constructor retained-state-policy
  field
    shellAdmissible :
      PhysicalTriadState carrier N → Set
    nonzeroModes :
      PhysicalTriadState carrier N → Set
    positiveSpectralWeight :
      PhysicalTriadState carrier N → Set
    phaseCompatible :
      PhysicalTriadState carrier N → Set
    parityCompatible :
      PhysicalTriadState carrier N → Set
    orientationCompatible :
      PhysicalTriadState carrier N → Set

open RetainedStatePolicy public

record RetainedPhysicalTriad
    {carrier : TriadStateCarrier}
    {N : Nat}
    (policy : RetainedStatePolicy carrier N) : Set where
  constructor retained-physical-triad
  field
    state : PhysicalTriadState carrier N
    shellAdmissibleProof : shellAdmissible policy state
    nonzeroModesProof : nonzeroModes policy state
    positiveSpectralWeightProof : positiveSpectralWeight policy state
    phaseCompatibleProof : phaseCompatible policy state
    parityCompatibleProof : parityCompatible policy state
    orientationCompatibleProof : orientationCompatible policy state

open RetainedPhysicalTriad public

------------------------------------------------------------------------
-- Stage-3 allocation.
--
-- Predicates may overlap analytically.  Exact finite ownership is obtained by
-- a deterministic priority:
--
--   forced-tail > transition > adversarial > residual.
--
-- Residual is the proved fallback when none of the three explicit predicates
-- fires; it is not a fourth enumerated combinatorial family.
------------------------------------------------------------------------

data Stage3Class : Set where
  forcedTail transition adversarial residual : Stage3Class

record Stage3GeometricPredicates
    {carrier : TriadStateCarrier}
    {N : Nat}
    (retainedPolicy : RetainedStatePolicy carrier N) : Set₁ where
  constructor stage3-geometric-predicates
  field
    ForcedTail Transition Adversarial Residual :
      RetainedPhysicalTriad retainedPolicy → Set

    forcedTail? transition? adversarial? :
      RetainedPhysicalTriad retainedPolicy → Bool

    forcedTailTrueSound :
      ∀ τ → forcedTail? τ ≡ true → ForcedTail τ
    transitionTrueSound :
      ∀ τ → transition? τ ≡ true → Transition τ
    adversarialTrueSound :
      ∀ τ → adversarial? τ ≡ true → Adversarial τ

    residualFallbackSound :
      ∀ τ →
      forcedTail? τ ≡ false →
      transition? τ ≡ false →
      adversarial? τ ≡ false →
      Residual τ

open Stage3GeometricPredicates public

ClassPredicate :
  ∀ {carrier N}
    {retainedPolicy : RetainedStatePolicy carrier N} →
  Stage3GeometricPredicates retainedPolicy →
  Stage3Class →
  RetainedPhysicalTriad retainedPolicy → Set
ClassPredicate geometry forcedTail = ForcedTail geometry
ClassPredicate geometry transition = Transition geometry
ClassPredicate geometry adversarial = Adversarial geometry
ClassPredicate geometry residual = Residual geometry

allocateStage3 :
  ∀ {carrier N}
    {retainedPolicy : RetainedStatePolicy carrier N} →
  Stage3GeometricPredicates retainedPolicy →
  RetainedPhysicalTriad retainedPolicy →
  Stage3Class
allocateStage3 geometry τ with forcedTail? geometry τ
... | true = forcedTail
... | false with transition? geometry τ
...   | true = transition
...   | false with adversarial? geometry τ
...     | true = adversarial
...     | false = residual

data AllocationEvidence
    {carrier : TriadStateCarrier}
    {N : Nat}
    {retainedPolicy : RetainedStatePolicy carrier N}
    (geometry : Stage3GeometricPredicates retainedPolicy)
    (τ : RetainedPhysicalTriad retainedPolicy) :
    Stage3Class → Set where

  allocatedForcedTail :
    forcedTail? geometry τ ≡ true →
    ForcedTail geometry τ →
    AllocationEvidence geometry τ forcedTail

  allocatedTransition :
    forcedTail? geometry τ ≡ false →
    transition? geometry τ ≡ true →
    Transition geometry τ →
    AllocationEvidence geometry τ transition

  allocatedAdversarial :
    forcedTail? geometry τ ≡ false →
    transition? geometry τ ≡ false →
    adversarial? geometry τ ≡ true →
    Adversarial geometry τ →
    AllocationEvidence geometry τ adversarial

  allocatedResidual :
    forcedTail? geometry τ ≡ false →
    transition? geometry τ ≡ false →
    adversarial? geometry τ ≡ false →
    Residual geometry τ →
    AllocationEvidence geometry τ residual

allocationSound :
  ∀ {carrier N}
    {retainedPolicy : RetainedStatePolicy carrier N} →
  (geometry : Stage3GeometricPredicates retainedPolicy) →
  (τ : RetainedPhysicalTriad retainedPolicy) →
  AllocationEvidence geometry τ (allocateStage3 geometry τ)
allocationSound geometry τ with forcedTail? geometry τ
... | true =
  allocatedForcedTail refl
    (forcedTailTrueSound geometry τ refl)
... | false with transition? geometry τ
...   | true =
    allocatedTransition refl refl
      (transitionTrueSound geometry τ refl)
...   | false with adversarial? geometry τ
...     | true =
      allocatedAdversarial refl refl refl
        (adversarialTrueSound geometry τ refl)
...     | false =
      allocatedResidual refl refl refl
        (residualFallbackSound geometry τ refl refl refl)

allocationCoverage :
  ∀ {carrier N}
    {retainedPolicy : RetainedStatePolicy carrier N} →
  (geometry : Stage3GeometricPredicates retainedPolicy) →
  (τ : RetainedPhysicalTriad retainedPolicy) →
  Σ Stage3Class (λ class → AllocationEvidence geometry τ class)
allocationCoverage geometry τ =
  allocateStage3 geometry τ , allocationSound geometry τ

allocationPredicateSound :
  ∀ {carrier N}
    {retainedPolicy : RetainedStatePolicy carrier N}
    {geometry : Stage3GeometricPredicates retainedPolicy}
    {τ : RetainedPhysicalTriad retainedPolicy}
    {class : Stage3Class} →
  AllocationEvidence geometry τ class →
  ClassPredicate geometry class τ
allocationPredicateSound (allocatedForcedTail decision proof) = proof
allocationPredicateSound (allocatedTransition prior decision proof) = proof
allocationPredicateSound
  (allocatedAdversarial first second decision proof) = proof
allocationPredicateSound
  (allocatedResidual first second third proof) = proof

allocationUnique :
  ∀ {carrier N}
    {retainedPolicy : RetainedStatePolicy carrier N}
    {geometry : Stage3GeometricPredicates retainedPolicy}
    {τ : RetainedPhysicalTriad retainedPolicy}
    {first second : Stage3Class} →
  allocateStage3 geometry τ ≡ first →
  allocateStage3 geometry τ ≡ second →
  first ≡ second
allocationUnique firstEquality secondEquality =
  trans (sym firstEquality) secondEquality

data ExplicitStage3Class : Set where
  explicitForcedTail explicitTransition explicitAdversarial :
    ExplicitStage3Class

explicitToStage3Class : ExplicitStage3Class → Stage3Class
explicitToStage3Class explicitForcedTail = forcedTail
explicitToStage3Class explicitTransition = transition
explicitToStage3Class explicitAdversarial = adversarial

record NonResidualAllocation
    {carrier : TriadStateCarrier}
    {N : Nat}
    {retainedPolicy : RetainedStatePolicy carrier N}
    (geometry : Stage3GeometricPredicates retainedPolicy)
    (τ : RetainedPhysicalTriad retainedPolicy) : Set where
  constructor non-residual-allocation
  field
    explicitClass : ExplicitStage3Class
    allocatedExplicitly :
      allocateStage3 geometry τ ≡ explicitToStage3Class explicitClass

open NonResidualAllocation public

physicalTriadStateSeparatedFromIncidence : Bool
physicalTriadStateSeparatedFromIncidence = true

physicalTriadStateSeparatedFromIncidenceIsTrue :
  physicalTriadStateSeparatedFromIncidence ≡ true
physicalTriadStateSeparatedFromIncidenceIsTrue = refl

deterministicStage3AllocationImplemented : Bool
deterministicStage3AllocationImplemented = true

deterministicStage3AllocationImplementedIsTrue :
  deterministicStage3AllocationImplemented ≡ true
deterministicStage3AllocationImplementedIsTrue = refl

retainedStage3CoverageImplemented : Bool
retainedStage3CoverageImplemented = true

retainedStage3CoverageImplementedIsTrue :
  retainedStage3CoverageImplemented ≡ true
retainedStage3CoverageImplementedIsTrue = refl
