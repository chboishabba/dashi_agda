module DASHI.Mathematics.NumberTheory.PartitionErdosBishopUpperMajorantBoundaryExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _∸_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat.Base using (_≤_)

import RealProperties as BishopProperties
import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke
import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bishop
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Foundations.BishopNatSquareRootRegularFloorExact as SquareRoot
import DASHI.Foundations.BishopNatSquareRootNonnegativeExact as SquareRootNN
import DASHI.Foundations.BishopVendoredSubmoduleProvenanceExact as Vendored
import DASHI.Mathematics.NumberTheory.FiniteDivisorSumExact as Divisor
import DASHI.Mathematics.NumberTheory.PartitionDivisorSumRegroupingExact as Regroup
import DASHI.Mathematics.NumberTheory.PartitionErdosDivisorSumRecurrenceExact as Recurrence
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopGeometricKernelBridgeExact as GeometricBridge

bishopFold : ∀ {A : Set} → (A → Bishop.Bishopℝ) → List A → Bishop.Bishopℝ
bishopFold weight [] = Bishop.bishopZero
bishopFold weight (x ∷ xs) = Bishop.bishopAdd (weight x) (bishopFold weight xs)

record ErdosBishopUpperMajorantData : Set₁ where
  field
    elementaryData : Elementary.BishopElementaryPowerSeriesData
    natEmbed : Nat → Bishop.Bishopℝ
    natEmbedMul : ∀ left right →
      Bishop.BishopEquivalent
        (natEmbed (left * right))
        (Bishop.bishopMul (natEmbed left) (natEmbed right))
    natEmbedNonnegative : ∀ n →
      Bishop.BishopLessEqual Bishop.bishopZero (natEmbed n)
    erdosConstant : Bishop.Bishopℝ
    erdosConstantPositive : Bishop.BishopStrictLess Bishop.bishopZero erdosConstant

open ErdosBishopUpperMajorantData public

sqrtNat : ErdosBishopUpperMajorantData → Nat → Bishop.Bishopℝ
sqrtNat dataSet n = SquareRoot.canonicalFloorSquareRootReal n

sqrtNatNonnegativeReceipt :
  (dataSet : ErdosBishopUpperMajorantData) →
  ∀ n → Bishop.BishopLessEqual Bishop.bishopZero (sqrtNat dataSet n)
sqrtNatNonnegativeReceipt dataSet n =
  BishopProperties.nonNegx⇒0≤x
    (SquareRootNN.canonicalFloorSquareRootNonnegative n)

exponentialMajorant : ErdosBishopUpperMajorantData → Nat → Bishop.Bishopℝ
exponentialMajorant dataSet n =
  Elementary.bishopExp
    (elementaryData dataSet)
    (Bishop.bishopMul (erdosConstant dataSet) (sqrtNat dataSet n))

weightedExponentialResidual :
  (dataSet : ErdosBishopUpperMajorantData) → Nat → Bishop.Bishopℝ
weightedExponentialResidual dataSet n =
  bishopFold
    (λ r → Bishop.bishopMul
      (natEmbed dataSet (Divisor.sigma1 r))
      (exponentialMajorant dataSet (n ∸ r)))
    (Hecke.oneTo n)

record ErdosBishopUpperMajorantAnalyticInputs
    (dataSet : ErdosBishopUpperMajorantData) : Set₁ where
  field
    embeddedRecurrence : ∀ n →
      Bishop.BishopEquivalent
        (natEmbed dataSet (n * Regroup.partitionCount n))
        (bishopFold
          (λ r → Bishop.bishopMul
            (natEmbed dataSet (Divisor.sigma1 r))
            (natEmbed dataSet (Regroup.partitionCount (n ∸ r))))
          (Hecke.oneTo n))

    residualMajorantTransfer : ∀ n →
      (∀ r → r ∈ Hecke.oneTo n →
        Bishop.BishopLessEqual
          (natEmbed dataSet (Regroup.partitionCount (n ∸ r)))
          (exponentialMajorant dataSet (n ∸ r))) →
      Bishop.BishopLessEqual
        (bishopFold
          (λ r → Bishop.bishopMul
            (natEmbed dataSet (Divisor.sigma1 r))
            (natEmbed dataSet (Regroup.partitionCount (n ∸ r))))
          (Hecke.oneTo n))
        (weightedExponentialResidual dataSet n)

    sqrtNatSquaresToEmbeddedNat : ∀ n →
      Bishop.BishopEquivalent
        (Bishop.bishopMul (sqrtNat dataSet n) (sqrtNat dataSet n))
        (natEmbed dataSet n)

    erdosKernelEstimate : ∀ n →
      Bishop.BishopLessEqual
        (weightedExponentialResidual dataSet n)
        (Bishop.bishopMul (natEmbed dataSet n) (exponentialMajorant dataSet n))

    positiveNatScaleCancel : ∀ {n : Nat} →
      suc zero ≤ n →
      ∀ {left right : Bishop.Bishopℝ} →
      Bishop.BishopLessEqual
        (Bishop.bishopMul (natEmbed dataSet n) left)
        (Bishop.bishopMul (natEmbed dataSet n) right) →
      Bishop.BishopLessEqual left right

open ErdosBishopUpperMajorantAnalyticInputs public

finiteRecurrenceReceipt :
  (n : Nat) → n * Regroup.partitionCount n ≡ Regroup.divisorSumRHS n
finiteRecurrenceReceipt = Recurrence.canonicalErdosDivisorSumRecurrence

finiteGeometricInfrastructureReceipt : GeometricBridge.ErdosWeightedGeometricFrontier
finiteGeometricInfrastructureReceipt = GeometricBridge.currentWeightedGeometricFrontier

data ErdosKernelProofRole : Set where
  squareRootSemanticSquareLaw : ErdosKernelProofRole
  squareRootTangentInequality : ErdosKernelProofRole
  exponentialAdditivityAndMonotonicity : ErdosKernelProofRole
  degreeOneWeightedGeometricPointwiseDomination : ErdosKernelProofRole
  degreeOneWeightedGeometricReciprocalSquareBound : ErdosKernelProofRole
  baselSumPiSquaredOverSix : ErdosKernelProofRole
  constantPiSqrtTwoThirdsIdentification : ErdosKernelProofRole
