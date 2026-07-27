module DASHI.Physics.Closure.NSTriadKNKiriukhinSymmetricStretchingCompanionAudit where

------------------------------------------------------------------------
-- PROVENANCE
-- Author: Oleg Kiriukhin.
-- Title: "Orbit-Level Stretching in Cubic Fourier-Galerkin Navier-Stokes:
-- Sharp Incidence, Spectral Decay, and a Continuation Criterion".
-- Venue/year: arXiv:2603.23293v1, submitted 24 March 2026.
-- DOI: 10.48550/arXiv.2603.23293.
-- Uses: the symmetric decomposition S = A + V, the sharp orbit-incidence
-- estimate, the deterministic Sobolev-class infinity-norm bound for V_N,
-- and the orbit-level continuation criterion.
-- Relationship: records the companion symmetric-part theorem and audits
-- whether it supplies an independent Grafakos--Torres partial-adjoint
-- homogeneity equation.  It does not: V sees only (M + M^T)/2 and is blind
-- to an arbitrarily large antisymmetric raw transfer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_<_)
import Data.Integer.Base as Int

record SymmetricStretchingSourceReceipt : Set where
  constructor source-receipt
  field
    submittedDay : Nat
    submittedMonth : Nat
    submittedYear : Nat
    sobolevThresholdNumerator : Nat
    sobolevThresholdDenominator : Nat
    incidenceExponent : Nat
    deterministicCubicNormPower : Nat
    symmetricPartGovernsNetEnstrophyGrowth : Bool
    deterministicSymmetricInfinityBoundAvailable : Bool
    cutoffUniformForSAboveTwo : Bool
    continuationCriterionAvailable : Bool

open SymmetricStretchingSourceReceipt public

symmetricStretchingSourceReceipt : SymmetricStretchingSourceReceipt
symmetricStretchingSourceReceipt =
  source-receipt 24 3 2026 2 1 3 3 true true true true

record RawSymmetricIndependenceWitness : Set where
  constructor witness
  field
    rawOffDiagonalMagnitude : Nat
    rawRowAbsoluteSum : Nat
    rawColumnAbsoluteSum : Nat
    symmetricRowAbsoluteSum : Nat
    symmetricColumnAbsoluteSum : Nat
    rawMagnitudePositive : 0 < rawOffDiagonalMagnitude
    symmetricPartExactlyZero : symmetricRowAbsoluteSum ≡ 0
    symmetricColumnExactlyZero : symmetricColumnAbsoluteSum ≡ 0

open RawSymmetricIndependenceWitness public

-- Exact matrix witness:
--
--       M = [ 0   37 ]       M^T = [ 0  -37 ]
--           [ -37  0 ]             [ 37   0 ]
--
-- Hence V = (M + M^T)/2 = 0, while both raw row and column maxima are 37.
rawSymmetricIndependenceWitness : RawSymmetricIndependenceWitness
rawSymmetricIndependenceWitness =
  witness 37 37 37 0 0 (Data.Nat.Base.s≤s Data.Nat.Base.z≤n) refl refl

record SymmetricCompanionRankAudit : Set where
  constructor rank-audit
  field
    rawOutputRowRank : Nat
    threeWeightUnknownCount : Nat
    rowOnlyNullity : Nat
    companionAddsIndependentAdjointEquation : Bool
    rankAfterCompanion : Nat
    nullityAfterCompanion : Nat
    rankNullityBefore : rawOutputRowRank + rowOnlyNullity ≡ threeWeightUnknownCount
    rankNullityAfter : rankAfterCompanion + nullityAfterCompanion ≡ threeWeightUnknownCount
    antisymmetricBlindnessWitness : RawSymmetricIndependenceWitness

open SymmetricCompanionRankAudit public

symmetricCompanionRankAudit : SymmetricCompanionRankAudit
symmetricCompanionRankAudit =
  rank-audit 1 3 2 false 1 2 refl refl rawSymmetricIndependenceWitness

companionSymmetricBoundReducesTriadicNullity : Bool
companionSymmetricBoundReducesTriadicNullity = false

companionSymmetricBoundReducesTriadicNullityIsFalse :
  companionSymmetricBoundReducesTriadicNullity ≡ false
companionSymmetricBoundReducesTriadicNullityIsFalse = refl

companionUsefulForOrbitEnstrophyContinuation : Bool
companionUsefulForOrbitEnstrophyContinuation = true

companionUsefulForOrbitEnstrophyContinuationIsTrue :
  companionUsefulForOrbitEnstrophyContinuation ≡ true
companionUsefulForOrbitEnstrophyContinuationIsTrue = refl

firstPartialAdjointStillRequired secondPartialAdjointStillRequired : Bool
firstPartialAdjointStillRequired = true
secondPartialAdjointStillRequired = true
