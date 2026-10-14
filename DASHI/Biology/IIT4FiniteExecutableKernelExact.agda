module DASHI.Biology.IIT4FiniteExecutableKernelExact where

open import DASHI.Core.Prelude

import DASHI.Biology.IIT4FiniteCausalStructureExact as IIT4
import DASHI.Biology.IIT4FiniteProbabilityRepertoireExact as Prob
import DASHI.Biology.IIT4SystemPhiInputExact as Phi

------------------------------------------------------------------------
-- VERSIONED FINITE IIT-4 EXECUTION SURFACE
--
-- This file owns the typed interface between the exact finite carrier and an
-- executable scalar/reference implementation.  It deliberately separates the
-- 2023 Albantakis et al. system-phi definition from the 2026 Mayner et al.
-- intrinsic-information requirement.
--
-- 2023: phi_s = min(phi_c, phi_e) at the normalized MIP.
-- 2026: choose the same integration MIP first, then apply
--       phi_s = min(phi_c, phi_e, ii(s)).
--
-- The numerical logarithm remains an explicit external scalar backend; Agda
-- owns the finite carrier, version boundary, probability-domain obligations,
-- and receipt shape.  No Python result is promoted to a kernel proof here.
------------------------------------------------------------------------

data IIT4FormalismVersion : Set where
  iit4-2023 : IIT4FormalismVersion
  iit4-2026 : IIT4FormalismVersion

------------------------------------------------------------------------
-- 1. Probability-domain repair: a probability consumed by a logarithmic
--    backend must carry a nonzero denominator witness.
------------------------------------------------------------------------

record PositiveDenominatorFraction : Set where
  constructor positiveDenominatorFraction
  field
    numerator : Nat
    denominatorPredecessor : Nat

open PositiveDenominatorFraction public

denominator : PositiveDenominatorFraction → Nat
denominator fraction = suc (denominatorPredecessor fraction)

toProbabilityFraction :
  PositiveDenominatorFraction → Prob.ProbabilityFraction
toProbabilityFraction fraction =
  Prob.probabilityFraction (numerator fraction) (denominator fraction)

zeroDenominatorCannotInhabitPositiveFraction :
  (fraction : PositiveDenominatorFraction) →
  denominator fraction ≡ 0 → ⊥
zeroDenominatorCannotInhabitPositiveFraction fraction ()

------------------------------------------------------------------------
-- 2. Exact repertoire receipt supplied to the scalar backend.
--
-- Cause selectivity is Bayesian.  The cause informativeness term still uses
-- the forward effect repertoire p_e(current | cause), matching the IIT-4
-- equations rather than identifying cause and effect repertoires.
------------------------------------------------------------------------

record ExecutableCauseEffectStateReceipt
    (system : IIT4.FiniteCausalSystem) : Set₁ where
  constructor executableCauseEffectStateReceipt
  field
    currentState : IIT4.StateOf system
    specifiedCauseState : IIT4.StateOf system
    specifiedEffectState : IIT4.StateOf system

    causeSelectivity : PositiveDenominatorFraction
    effectSelectivity : PositiveDenominatorFraction

    causeForwardEffectProbability : PositiveDenominatorFraction
    currentUnconstrainedEffectProbability : PositiveDenominatorFraction
    effectUnconstrainedProbability : PositiveDenominatorFraction

    causeSelectionReceipt : String
    effectSelectionReceipt : String
    bayesianCauseReceipt : String

open ExecutableCauseEffectStateReceipt public

------------------------------------------------------------------------
-- 3. Directional partition evaluation receipt.
------------------------------------------------------------------------

record ExecutablePartitionReceipt
    (system : IIT4.FiniteCausalSystem) : Set₁ where
  constructor executablePartitionReceipt
  field
    partition : IIT4.SystemPartition system
    causePartitionedForwardProbability : PositiveDenominatorFraction
    effectPartitionedProbability : PositiveDenominatorFraction
    affectedConnectionCountPositiveWitness : Nat
    affectedConnectionCountIsPositive :
      IIT4.affectedConnectionCount partition
      ≡ suc affectedConnectionCountPositiveWitness
    partitionConstructionReceipt : String

open ExecutablePartitionReceipt public

------------------------------------------------------------------------
-- 4. Versioned system-phi receipt.
------------------------------------------------------------------------

record ExecutableSystemPhiReceipt
    (system : IIT4.FiniteCausalSystem) : Set₁ where
  constructor executableSystemPhiReceipt
  field
    formalismVersion : IIT4FormalismVersion
    specifiedState : ExecutableCauseEffectStateReceipt system
    candidatePartitions : List (ExecutablePartitionReceipt system)
    minimumPartition : ExecutablePartitionReceipt system

    -- Named scalar outputs are text receipts because this owner does not
    -- fabricate a real/logarithmic number type.
    phiCauseReceipt : String
    phiEffectReceipt : String
    phiSystem2023Receipt : String
    intrinsicDifferentiationCauseReceipt : String
    intrinsicDifferentiationEffectReceipt : String
    intrinsicInformationReceipt : String
    phiSystemReturnedReceipt : String

    mipSelectedBefore2026IntrinsicCap : Bool
    returnedValueIsUnnormalizedAtMIP : Bool
    numericalReceiptHash : String

open ExecutableSystemPhiReceipt public

------------------------------------------------------------------------
-- 5. Version boundary / authority firewall.
------------------------------------------------------------------------

record IIT4ExecutableKernelBoundary : Set where
  constructor iit4ExecutableKernelBoundary
  field
    systemPhi2023And2026AreVersioned : Bool
    causeSelectivityIsBayesian : Bool
    causeInformativenessUsesForwardEffectRepertoire : Bool
    directionalPartitionCausallyMarginalizesCutInputs : Bool
    mipSearchUsesNormalizedIntegration : Bool
    iit42026IntrinsicRequirementAppliedAfterMIP : Bool
    deterministicSystemMayHavePositive2023PhiS : Bool
    deterministicSystemHasZero2026PhiSWhenDifferentiationZero : Bool
    positiveDenominatorRequiredForLogarithmicInput : Bool
    pythonReceiptEqualsAgdaKernelProofByDefinition : Bool
    fullDistinctionRelationBigPhiImplementedHere : Bool

open IIT4ExecutableKernelBoundary public

canonicalIIT4ExecutableKernelBoundary : IIT4ExecutableKernelBoundary
canonicalIIT4ExecutableKernelBoundary =
  iit4ExecutableKernelBoundary
    true true true true true true true true true
    false false

pythonReceiptIsNotKernelProof :
  pythonReceiptEqualsAgdaKernelProofByDefinition
    canonicalIIT4ExecutableKernelBoundary ≡ false
pythonReceiptIsNotKernelProof = refl

systemPhiVersionBoundaryPaid :
  systemPhi2023And2026AreVersioned
    canonicalIIT4ExecutableKernelBoundary ≡ true
systemPhiVersionBoundaryPaid = refl

fullPhiStructureRemainsDownstream :
  fullDistinctionRelationBigPhiImplementedHere
    canonicalIIT4ExecutableKernelBoundary ≡ false
fullPhiStructureRemainsDownstream = refl
