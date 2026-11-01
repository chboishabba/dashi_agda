module DASHI.Physics.Closure.NSTriadKNHHBadLiteralDuhamelAdapterRound58Exact where

------------------------------------------------------------------------
-- ROUND 58 — connect the existing literal three-mechanism carrier to the
-- Round-57 raw Duhamel record.
--
-- This is an adapter only.  It does not construct a Navier--Stokes trajectory
-- or prove the analytic transfer fields of `PhysicalDyadicThreeMechanismTransfer`.
-- It removes the duplicate record boundary so that any future physical witness
-- immediately supplies the Round-57 inherited/generated/leakage object.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNHHBadRawVariableCapacityRound53Exact as Raw
import DASHI.Physics.Closure.NSTriadKNHHBadDyadicThreeMechanismRecurrenceRound48Exact as Three
import DASHI.Physics.Closure.NSTriadKNHHBadDyadicInheritedHalfRound48Exact as Half

constant : ℚ → Nat → ℚ
constant value _ = value

asLiteralDuhamel :
  Three.PhysicalDyadicThreeMechanismTransfer →
  Raw.PhysicalGeneralVariableDefectDuhamel
asLiteralDuhamel physical = record
  { parameter = Three.parameter physical
  ; defectRate = Three.defectRate physical
  ; inherited = Three.inheritedAt physical
  ; generated = Three.generated physical
  ; leakage = Three.leakage physical
  ; alpha = constant (Three.alpha physical)
  ; forcing = constant (Three.beta physical)
  ; defectRateNonnegative = Three.defectRateNonnegative physical
  ; inheritedNonnegative =
      Half.inheritedDefectNonnegative
        (Three.inheritedData physical)
  ; generatedNonnegative = Three.generatedNonnegative physical
  ; leakageNonnegative = Three.leakageNonnegative physical
  ; alphaNonnegative = λ _ → Three.alphaNonnegative physical
  ; forcingNonnegative = λ _ → Three.betaNonnegative physical
  ; successorDecomposition = λ q →
      Three.successorDecomposition physical q
  ; inheritedTransfer = λ q →
      Half.inverseShellInheritedDefectHalvesModuloCoefficient
        (Three.inheritedData physical) q
  ; generatedLeakageTransfer = λ q →
      Three.generatedAndLeakageForcing physical q
  }

adapterPreservesLiteralSuccessorDecomposition : Bool
adapterPreservesLiteralSuccessorDecomposition = true

adapterPreservesLiteralSuccessorDecompositionIsTrue :
  adapterPreservesLiteralSuccessorDecomposition ≡ true
adapterPreservesLiteralSuccessorDecompositionIsTrue = refl

adapterPreservesLiteralGeneratedLeakageTransfer : Bool
adapterPreservesLiteralGeneratedLeakageTransfer = true

adapterPreservesLiteralGeneratedLeakageTransferIsTrue :
  adapterPreservesLiteralGeneratedLeakageTransfer ≡ true
adapterPreservesLiteralGeneratedLeakageTransferIsTrue = refl

-- The adapter is not itself the missing PDE witness.
physicalDuhamelAdapterNeedsSourceTransfer : Bool
physicalDuhamelAdapterNeedsSourceTransfer = true

physicalDuhamelAdapterNeedsSourceTransferIsTrue :
  physicalDuhamelAdapterNeedsSourceTransfer ≡ true
physicalDuhamelAdapterNeedsSourceTransferIsTrue = refl
