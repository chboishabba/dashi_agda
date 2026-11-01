module DASHI.Cognition.ClopenPsychologicalSupervoxel where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Data.Empty using (⊥)

import Base369 as Base
import DASHI.Algebra.BalancedTernary as BT
import DASHI.Cognition.PhaseEnrichedTrit as Phase
import DASHI.Cognition.ReflexivePresentationFamily as Presentation
import DASHI.Foundations.ConstraintClopenRefinement as Refinement

------------------------------------------------------------------------
-- Psychological zero as a coarse clopen-supervoxel constraint.
------------------------------------------------------------------------

data PsychologicalConstraint : Set where
  publicZeroConstraint : PsychologicalConstraint
  inactiveZeroConstraint : PsychologicalConstraint
  balancedOppositionConstraint : PsychologicalConstraint
  activeAppraisalConstraint : PsychologicalConstraint
  rapidSwitchingConstraint : PsychologicalConstraint
  phaseCancellationConstraint : PsychologicalConstraint
  socialInhibitionConstraint : PsychologicalConstraint
  insufficientEvidenceConstraint : PsychologicalConstraint
  memoryFreezeConstraint : PsychologicalConstraint

Satisfies :
  Presentation.PsychologicalHiddenState →
  PsychologicalConstraint →
  Set
Satisfies state publicZeroConstraint =
  Presentation.balancedProjection state ≡ BT.zero
Satisfies state inactiveZeroConstraint =
  Presentation.salience state ≡ zero
Satisfies state balancedOppositionConstraint =
  Presentation.rememberedValue state ≡ Phase.balancedOpposition
Satisfies state activeAppraisalConstraint =
  Presentation.contextDepth state ≡ suc zero
Satisfies state rapidSwitchingConstraint =
  Presentation.wavePhase state ≡ Phase.phase2
Satisfies state phaseCancellationConstraint =
  Presentation.rememberedValue state
    ≡ Phase.phaseShiftedBalancedOpposition
Satisfies state socialInhibitionConstraint =
  Presentation.avoidedValue state ≡ Base.tri-high
Satisfies state insufficientEvidenceConstraint =
  Presentation.confidence state ≡ zero
Satisfies state memoryFreezeConstraint =
  Presentation.expectedValue state ≡ Phase.negativeDominant

psychologicalConstraintSystem : Refinement.ConstraintSystem
psychologicalConstraintSystem =
  record
    { State = Presentation.PsychologicalHiddenState
    ; Constraint = PsychologicalConstraint
    ; satisfies = Satisfies
    }

balancedOppositionRefinesPublicZero :
  Refinement.FineExtendsCoarse
    psychologicalConstraintSystem
    publicZeroConstraint
    balancedOppositionConstraint
balancedOppositionRefinesPublicZero =
  record
    { forgetConstraint = λ {state} remembered≡balanced →
        trans
          (cong Phase.observeTrit remembered≡balanced)
          Phase.balancedOppositionObservesZero
    }

phaseCancellationRefinesPublicZero :
  Refinement.FineExtendsCoarse
    psychologicalConstraintSystem
    publicZeroConstraint
    phaseCancellationConstraint
phaseCancellationRefinesPublicZero =
  record
    { forgetConstraint = λ {state} remembered≡shifted →
        trans
          (cong Phase.observeTrit remembered≡shifted)
          Phase.phaseShiftedBalancedObservesZero
    }

------------------------------------------------------------------------
-- Distinct fine dynamics inside the same public zero ball.
------------------------------------------------------------------------

data ZeroDynamicsClass : Set where
  stableInactiveDynamics : ZeroDynamicsClass
  balancedBifurcationDynamics : ZeroDynamicsClass
  oscillatoryDynamics : ZeroDynamicsClass
  phaseCancelledDynamics : ZeroDynamicsClass
  mixtureDynamics : ZeroDynamicsClass
  boundaryDriftDynamics : ZeroDynamicsClass

record PsychologicalZeroSubvoxel : Set where
  constructor psychologicalZeroSubvoxel
  field
    hidden : Presentation.PsychologicalHiddenState
    classification : ZeroDynamicsClass
    coarseZero : Presentation.balancedProjection hidden ≡ BT.zero

open PsychologicalZeroSubvoxel public

phaseShiftedHiddenState : Presentation.PsychologicalHiddenState
phaseShiftedHiddenState =
  Presentation.psychologicalHiddenState
    (Presentation.reasoningState Presentation.canonicalHiddenState)
    (Presentation.avoidedValue Presentation.canonicalHiddenState)
    Phase.phaseShiftedBalancedOpposition
    (Presentation.expectedValue Presentation.canonicalHiddenState)
    (Presentation.contextDepth Presentation.canonicalHiddenState)
    (Presentation.salience Presentation.canonicalHiddenState)
    (Presentation.confidence Presentation.canonicalHiddenState)
    Phase.phase1
    (Presentation.activeAttractorCount Presentation.canonicalHiddenState)

balancedZeroSubvoxel : PsychologicalZeroSubvoxel
balancedZeroSubvoxel =
  psychologicalZeroSubvoxel
    Presentation.canonicalHiddenState
    balancedBifurcationDynamics
    refl

phaseCancelledZeroSubvoxel : PsychologicalZeroSubvoxel
phaseCancelledZeroSubvoxel =
  psychologicalZeroSubvoxel
    phaseShiftedHiddenState
    phaseCancelledDynamics
    refl

balanced≢phaseCancelled :
  balancedBifurcationDynamics ≡ phaseCancelledDynamics → ⊥
balanced≢phaseCancelled ()

record SamePublicZeroDifferentDynamics : Set where
  field
    left right : PsychologicalZeroSubvoxel
    dynamicsDiffer : classification left ≡ classification right → ⊥

canonicalSamePublicZeroDifferentDynamics :
  SamePublicZeroDifferentDynamics
canonicalSamePublicZeroDifferentDynamics =
  record
    { left = balancedZeroSubvoxel
    ; right = phaseCancelledZeroSubvoxel
    ; dynamicsDiffer = balanced≢phaseCancelled
    }

record ZeroSupervoxel : Set₁ where
  field
    parentConstraint : PsychologicalConstraint
    childConstraints : List PsychologicalConstraint
    balancedChildRefinesParent :
      Refinement.FineExtendsCoarse
        psychologicalConstraintSystem
        parentConstraint
        balancedOppositionConstraint
    phaseChildRefinesParent :
      Refinement.FineExtendsCoarse
        psychologicalConstraintSystem
        parentConstraint
        phaseCancellationConstraint

open ZeroSupervoxel public

canonicalZeroSupervoxel : ZeroSupervoxel
canonicalZeroSupervoxel =
  record
    { parentConstraint = publicZeroConstraint
    ; childConstraints =
        inactiveZeroConstraint
        ∷ balancedOppositionConstraint
        ∷ activeAppraisalConstraint
        ∷ rapidSwitchingConstraint
        ∷ phaseCancellationConstraint
        ∷ socialInhibitionConstraint
        ∷ insufficientEvidenceConstraint
        ∷ memoryFreezeConstraint
        ∷ []
    ; balancedChildRefinesParent = balancedOppositionRefinesPublicZero
    ; phaseChildRefinesParent = phaseCancellationRefinesPublicZero
    }

------------------------------------------------------------------------
-- A coarse zero statistic records mass, not internal mechanism.
------------------------------------------------------------------------

record ZeroPushforwardSummary : Set where
  constructor zeroPushforwardSummary
  field
    stableCount : Nat
    balancedCount : Nat
    oscillatoryCount : Nat
    phaseCancelledCount : Nat
    mixtureCount : Nat
    boundaryCount : Nat
    totalCount : Nat
    totalDecomposes :
      totalCount ≡
        stableCount + balancedCount + oscillatoryCount
          + phaseCancelledCount + mixtureCount + boundaryCount

open ZeroPushforwardSummary public

canonicalZeroPushforwardSummary : ZeroPushforwardSummary
canonicalZeroPushforwardSummary =
  zeroPushforwardSummary 1 1 1 1 1 1 6 refl

record ClopenPsychologyBoundary : Set where
  constructor clopenPsychologyBoundary
  field
    publicZeroIsAtomic : Bool
    publicZeroIsAtomicIsFalse : publicZeroIsAtomic ≡ false
    subvoxelMechanismClinicallyValidated : Bool
    subvoxelMechanismClinicallyValidatedIsFalse :
      subvoxelMechanismClinicallyValidated ≡ false

canonicalClopenPsychologyBoundary : ClopenPsychologyBoundary
canonicalClopenPsychologyBoundary =
  clopenPsychologyBoundary false refl false refl
