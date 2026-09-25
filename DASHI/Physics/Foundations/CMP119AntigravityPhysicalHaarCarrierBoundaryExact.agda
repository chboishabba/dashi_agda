{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityPhysicalHaarCarrierBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _<ℝ_; 0ℝ)
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealTwoJSourceExact as RealCMP119

------------------------------------------------------------------------
-- PHYSICAL HAAR CARRIER BOUNDARY
--
-- A finite lattice with compact gauge group SU(2) still has a continuous
-- configuration space SU(2)^E.  "Finite cutoff" therefore does not make the
-- literal product-Haar integral a finite atomic or generally rational-valued
-- integral.
--
-- The antigravity rational calculus remains useful for exact algebra,
-- convention checks and certified rational coordinates.  Physical promotion
-- requires a same-family transport into the repository's existing REAL CMP119
-- finite expectation lane.
------------------------------------------------------------------------

record RationalToRealAntigravitySourceTransport : Set₁ where
  field
    rationalPartition : ℚ
    rationalQuantumTrace : ℚ

    realPartition : ℝ
    realQuantumTrace : ℝ

    rationalPartitionPositive : Set
    rationalQuantumTraceNegative : Set

    SameCMP119FiniteFamily : Set
    sameCMP119FiniteFamily : SameCMP119FiniteFamily

    PartitionTransport : Set
    partitionTransport : PartitionTransport

    QuantumTraceTransport : Set
    quantumTraceTransport : QuantumTraceTransport

    realPartitionPositive :
      0ℝ <ℝ realPartition

    realQuantumTraceNegative :
      realQuantumTrace <ℝ 0ℝ

open RationalToRealAntigravitySourceTransport public

finiteLatticeImpliesFiniteConfigurationSpace : Bool
finiteLatticeImpliesFiniteConfigurationSpace = false

finiteLatticeImpliesFiniteConfigurationSpaceIsFalse :
  finiteLatticeImpliesFiniteConfigurationSpace ≡ false
finiteLatticeImpliesFiniteConfigurationSpaceIsFalse = refl

exactFiniteAtomicQuadratureIsLiteralCompactHaar : Bool
exactFiniteAtomicQuadratureIsLiteralCompactHaar = false

exactFiniteAtomicQuadratureIsLiteralCompactHaarIsFalse :
  exactFiniteAtomicQuadratureIsLiteralCompactHaar ≡ false
exactFiniteAtomicQuadratureIsLiteralCompactHaarIsFalse = refl

rationalHaarFunctionalAutomaticallyIsPhysicalSU2ProductHaar : Bool
rationalHaarFunctionalAutomaticallyIsPhysicalSU2ProductHaar = false

rationalHaarFunctionalAutomaticallyIsPhysicalSU2ProductHaarIsFalse :
  rationalHaarFunctionalAutomaticallyIsPhysicalSU2ProductHaar ≡ false
rationalHaarFunctionalAutomaticallyIsPhysicalSU2ProductHaarIsFalse = refl

realCMP119FiniteExpectationLaneAlreadyExists : Bool
realCMP119FiniteExpectationLaneAlreadyExists = true

realCMP119FiniteExpectationLaneAlreadyExistsIsTrue :
  realCMP119FiniteExpectationLaneAlreadyExists ≡ true
realCMP119FiniteExpectationLaneAlreadyExistsIsTrue = refl

physicalAntigravitySourceRequiresRealHaarTransport : Bool
physicalAntigravitySourceRequiresRealHaarTransport = true

physicalAntigravitySourceRequiresRealHaarTransportIsTrue :
  physicalAntigravitySourceRequiresRealHaarTransport ≡ true
physicalAntigravitySourceRequiresRealHaarTransportIsTrue = refl
