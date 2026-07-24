module DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _/_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (baseBelowBasePlusRemainder)

------------------------------------------------------------------------
-- Exact geometric majorant for the rooted-trace entropy carrier.
--
-- Eight choices per traversal step and a suppression factor 1/16 per step give
-- shell ratio 1/2.  The finite KP shell sum is therefore bounded by two, with
-- an explicit nonnegative tail.  Passing from finite partial sums to the
-- physical infinite polymer sum still requires the physical trace injection
-- and the standard geometric-limit theorem.
------------------------------------------------------------------------

half twoℚ : ℚ
half = + 1 / 2
twoℚ = 1ℚ + 1ℚ

halfPower : Nat → ℚ
halfPower zero = 1ℚ
halfPower (suc depth) = half * halfPower depth

traceShellPartialSum : Nat → ℚ
traceShellPartialSum zero = 0ℚ
traceShellPartialSum (suc depth) =
  traceShellPartialSum depth + halfPower depth

halfNonnegative : 0ℚ ≤ half
halfNonnegative =
  let
    instance
      halfNonnegativeInstance : NonNegative half
      halfNonnegativeInstance = ℚP.normalize-nonNeg 1 2
  in
  ℚP.nonNegative⁻¹ half

halfPowerNonnegative : ∀ depth → 0ℚ ≤ halfPower depth
halfPowerNonnegative zero =
  let
    instance
      oneNonnegative : NonNegative 1ℚ
      oneNonnegative = nonNegative ℚP.0≤1
  in
  ℚP.nonNegative⁻¹ 1ℚ
halfPowerNonnegative (suc depth) =
  let
    instance
      halfNonnegativeInstance : NonNegative half
      halfNonnegativeInstance = nonNegative halfNonnegative

      previousNonnegativeInstance : NonNegative (halfPower depth)
      previousNonnegativeInstance = nonNegative (halfPowerNonnegative depth)

      productNonnegative : NonNegative (half * halfPower depth)
      productNonnegative = ℚP.nonNeg*nonNeg⇒nonNeg half (halfPower depth)
  in
  ℚP.nonNegative⁻¹ (half * halfPower depth)

twoTimesHalfPowerNonnegative : ∀ depth →
  0ℚ ≤ twoℚ * halfPower depth
twoTimesHalfPowerNonnegative depth =
  let
    twoNonnegativeProof : 0ℚ ≤ twoℚ
    twoNonnegativeProof = ℚP.+-mono-≤ ℚP.0≤1 ℚP.0≤1

    instance
      twoNonnegative : NonNegative twoℚ
      twoNonnegative = nonNegative twoNonnegativeProof

      powerNonnegative : NonNegative (halfPower depth)
      powerNonnegative = nonNegative (halfPowerNonnegative depth)

      productNonnegative : NonNegative (twoℚ * halfPower depth)
      productNonnegative =
        ℚP.nonNeg*nonNeg⇒nonNeg twoℚ (halfPower depth)
  in
  ℚP.nonNegative⁻¹ (twoℚ * halfPower depth)

geometricStepAlgebra : ∀ partial power →
  partial + twoℚ * power ≡ twoℚ →
  (partial + power) + twoℚ * (half * power) ≡ twoℚ
geometricStepAlgebra partial power inductionHypothesis =
  trans
    (ℚRing.solve-∀ partial power)
    inductionHypothesis

traceShellGeometricIdentity : ∀ depth →
  traceShellPartialSum depth + twoℚ * halfPower depth ≡ twoℚ
traceShellGeometricIdentity zero = ℚRing.solve-∀
traceShellGeometricIdentity (suc depth) =
  geometricStepAlgebra
    (traceShellPartialSum depth)
    (halfPower depth)
    (traceShellGeometricIdentity depth)

traceShellPartialSumBelowTwo : ∀ depth →
  traceShellPartialSum depth ≤ twoℚ
traceShellPartialSumBelowTwo depth =
  subst
    (λ upper → traceShellPartialSum depth ≤ upper)
    (traceShellGeometricIdentity depth)
    (baseBelowBasePlusRemainder
      (traceShellPartialSum depth)
      (twoℚ * halfPower depth)
      (twoTimesHalfPowerNonnegative depth))

traceEntropySuppressionRatio : ℚ
traceEntropySuppressionRatio = + 8 / 16

traceEntropySuppressionRatioIsHalf :
  traceEntropySuppressionRatio ≡ half
traceEntropySuppressionRatioIsHalf = refl

traceShellGeometricIdentityLevel : ProofLevel
traceShellGeometricIdentityLevel = computed

finiteTraceKoteckyPreissBoundLevel : ProofLevel
finiteTraceKoteckyPreissBoundLevel = machineChecked

physicalTraceToPolymerWeightedSumLevel : ProofLevel
physicalTraceToPolymerWeightedSumLevel = conditional

infiniteTraceKoteckyPreissLimitLevel : ProofLevel
infiniteTraceKoteckyPreissLimitLevel = standardImported
