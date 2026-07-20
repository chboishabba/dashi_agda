module DASHI.Geometry.LargePosetContinuumLorentz31 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Unified.GRQuantumProofTerms as Legacy

------------------------------------------------------------------------
-- Large-poset / continuum derivation of a uniquely physical 3+1 signature.
--
-- The existing causal diamond is an exact finite model.  This authority adds
-- refinement, continuum reconstruction, dimension estimation, isotropy,
-- finite-speed, time orientation, and uniqueness among admissible signatures.
-- It deliberately does not infer 3+1 from the small diamond alone.

record SignatureCandidate : Set where
  constructor signature-candidate
  field
    spaceDimension : Nat
    timeDimension : Nat
open SignatureCandidate public

record IsPhysical31 (candidate : SignatureCandidate) : Set where
  constructor physical-31
  field
    spaceIsThree : spaceDimension candidate ≡ 3
    timeIsOne : timeDimension candidate ≡ 1
open IsPhysical31 public

record CausalRefinementSystem : Set₁ where
  field
    Refinement : Set
    FiniteEvent : Refinement → Set
    ContinuumEvent : Set

    causalFinite :
      (level : Refinement) →
      FiniteEvent level → FiniteEvent level → Set
    causalContinuum : ContinuumEvent → ContinuumEvent → Set

    refineEvent :
      (coarse fine : Refinement) →
      FiniteEvent coarse → FiniteEvent fine
    embedContinuum :
      (level : Refinement) → FiniteEvent level → ContinuumEvent

    ChainSample : Refinement → Set
    AntichainSample : Refinement → Set
    chainDepth : (level : Refinement) → ChainSample level → Nat
    antichainWidth : (level : Refinement) → AntichainSample level → Nat

    ContinuumTopology : Set
    ContinuumMeasure : Set
    DimensionEstimator : Set
    estimatedDimension : Refinement → DimensionEstimator → Nat

    refinementPreservesCausality : Set
    refinementPreservesCausalityProof : refinementPreservesCausality
    embeddingsBecomeDense : Set
    embeddingsBecomeDenseProof : embeddingsBecomeDense
    chainAntichainStatisticsConverge : Set
    chainAntichainStatisticsConvergeProof :
      chainAntichainStatisticsConverge
    continuumTopologyRecovered : Set
    continuumTopologyRecoveredProof : continuumTopologyRecovered
    continuumMeasureRecovered : Set
    continuumMeasureRecoveredProof : continuumMeasureRecovered
open CausalRefinementSystem public

record PhysicalLorentzSelection
  (system : CausalRefinementSystem) : Set₁ where
  field
    Candidate : Set
    candidateSignature : Candidate → SignatureCandidate
    admissible : Candidate → Set

    localLorentzianOrder : Set
    localLorentzianOrderProof : localLorentzianOrder
    stableDimensionLimit : Set
    stableDimensionLimitProof : stableDimensionLimit
    finitePropagationSpeed : Set
    finitePropagationSpeedProof : finitePropagationSpeed
    spatialIsotropy : Set
    spatialIsotropyProof : spatialIsotropy
    timeOrientability : Set
    timeOrientabilityProof : timeOrientability
    nondegenerateNullCone : Set
    nondegenerateNullConeProof : nondegenerateNullCone
    excludesMultipleTimeDirections : Set
    excludesMultipleTimeDirectionsProof : excludesMultipleTimeDirections

    classification :
      (candidate : Candidate) →
      admissible candidate →
      IsPhysical31 (candidateSignature candidate)

    uniquenessUpToCausalIsomorphism : Set
    uniquenessUpToCausalIsomorphismProof : uniquenessUpToCausalIsomorphism
open PhysicalLorentzSelection public

record LargePosetContinuumLorentz31Authority : Set₁ where
  field
    refinementSystem : CausalRefinementSystem
    physicalSelection : PhysicalLorentzSelection refinementSystem

    legacySurface : Legacy.ChainAntichainLorentzProof
    legacyClosed : Legacy.ChainAntichainLorentzClosed legacySurface

    continuumSpatialDimension : Nat
    continuumSpatialDimensionIsThree : continuumSpatialDimension ≡ 3
    continuumTimeDimension : Nat
    continuumTimeDimensionIsOne : continuumTimeDimension ≡ 1

    legacyDimensionAgreesWithContinuum : Set
    legacyDimensionAgreesWithContinuumProof :
      legacyDimensionAgreesWithContinuum
    finiteDiamondIsOnlyAConsistencyWitness : Set
    finiteDiamondIsOnlyAConsistencyWitnessProof :
      finiteDiamondIsOnlyAConsistencyWitness
open LargePosetContinuumLorentz31Authority public

classifyAdmissibleSignature :
  (authority : LargePosetContinuumLorentz31Authority) →
  (candidate : Candidate (physicalSelection authority)) →
  admissible (physicalSelection authority) candidate →
  IsPhysical31
    (candidateSignature (physicalSelection authority) candidate)
classifyAdmissibleSignature authority =
  classification (physicalSelection authority)

largePosetLegacySurface :
  LargePosetContinuumLorentz31Authority →
  Legacy.ChainAntichainLorentzProof
largePosetLegacySurface = legacySurface

largePosetLegacyClosed :
  (authority : LargePosetContinuumLorentz31Authority) →
  Legacy.ChainAntichainLorentzClosed (largePosetLegacySurface authority)
largePosetLegacyClosed = legacyClosed
