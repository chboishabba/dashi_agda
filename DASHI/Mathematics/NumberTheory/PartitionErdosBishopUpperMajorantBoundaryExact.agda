module DASHI.Mathematics.NumberTheory.PartitionErdosBishopUpperMajorantBoundaryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- P. Erdos,
-- "On an Elementary Proof of Some Asymptotic Formulas in the Theory of
-- Partitions", Annals of Mathematics (2) 43 (1942), 437--450.
-- DOI: 10.2307/1968802.
--
-- ERDOS UPPER-MAJORANT ANALYTIC HINGE
--
-- The finite recurrence is already closed in
-- PartitionErdosDivisorSumRecurrenceExact.  This owner isolates what remains
-- to turn that recurrence into an exponential majorant over the concrete
-- Bishop real carrier supplied by the pinned `vendor/bishop` submodule.
--
-- The intended source argument proves
--
--   p(n) < exp(c sqrt(n)),  c = pi sqrt(2/3),
--
-- by combining the recurrence with a square-root tangent estimate and a
-- weighted geometric/exponential kernel bound.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _∸_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat.Base using (_≤_)

import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke
import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bishop
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Foundations.BishopNatSquareRootApproximationExact as SquareRoot
import DASHI.Foundations.BishopVendoredSubmoduleProvenanceExact as Vendored
import DASHI.Mathematics.NumberTheory.FiniteDivisorSumExact as Divisor
import DASHI.Mathematics.NumberTheory.PartitionDivisorSumRegroupingExact as Regroup
import DASHI.Mathematics.NumberTheory.PartitionErdosDivisorSumRecurrenceExact as Recurrence
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopGeometricKernelBridgeExact as GeometricBridge

------------------------------------------------------------------------
-- Finite Bishop-valued folds.  This is only list recursion over the concrete
-- Bishop addition operation.

bishopFold : ∀ {A : Set} → (A → Bishop.Bishopℝ) → List A → Bishop.Bishopℝ
bishopFold weight [] = Bishop.bishopZero
bishopFold weight (x ∷ xs) =
  Bishop.bishopAdd (weight x) (bishopFold weight xs)

------------------------------------------------------------------------
-- Concrete candidate majorant and its finite residual convolution.

record ErdosBishopUpperMajorantData : Set₁ where
  field
    elementaryData : Elementary.BishopElementaryPowerSeriesData

    -- Canonical Nat embedding required to compare exact partition counts with
    -- the analytic majorant.  Algebra preservation is stated using Bishop's
    -- setoid equality rather than Agda propositional equality.
    natEmbed : Nat → Bishop.Bishopℝ
    natEmbedMul : ∀ left right →
      Bishop.BishopEquivalent
        (natEmbed (left * right))
        (Bishop.bishopMul (natEmbed left) (natEmbed right))

    natEmbedNonnegative : ∀ n →
      Bishop.BishopLessEqual Bishop.bishopZero (natEmbed n)

    -- Square root is no longer an arbitrary Bishop-valued function.  Each Nat
    -- radicand must supply a regular rational interval approximation, which is
    -- realized through the exact vendored `Real.mkℝ` constructor.
    sqrtApproximation :
      (n : Nat) → SquareRoot.BishopNatSquareRootApproximation n

    -- Positive exponential scale.  A later specialization identifies this
    -- with the Machin-pi realization of pi*sqrt(2/3).
    erdosConstant : Bishop.Bishopℝ
    erdosConstantPositive :
      Bishop.BishopStrictLess Bishop.bishopZero erdosConstant

open ErdosBishopUpperMajorantData public

sqrtNat : ErdosBishopUpperMajorantData → Nat → Bishop.Bishopℝ
sqrtNat dataSet n =
  SquareRoot.bishopNatSquareRootCandidate
    (sqrtApproximation dataSet n)

exponentialMajorant :
  ErdosBishopUpperMajorantData → Nat → Bishop.Bishopℝ
exponentialMajorant dataSet n =
  Elementary.bishopExp
    (elementaryData dataSet)
    (Bishop.bishopMul (erdosConstant dataSet) (sqrtNat dataSet n))

weightedExponentialResidual :
  (dataSet : ErdosBishopUpperMajorantData) → Nat → Bishop.Bishopℝ
weightedExponentialResidual dataSet n =
  bishopFold
    (λ r →
      Bishop.bishopMul
        (natEmbed dataSet (Divisor.sigma1 r))
        (exponentialMajorant dataSet (n ∸ r)))
    (Hecke.oneTo n)

------------------------------------------------------------------------
-- Typed analytic obligations.  These are not opaque `Set` flags: each field
-- states the exact inequality/equality needed by the induction step.

record ErdosBishopUpperMajorantAnalyticInputs
    (dataSet : ErdosBishopUpperMajorantData) : Set₁ where
  field
    -- Embed the already-proved exact Nat recurrence into Bishop arithmetic.
    embeddedRecurrence : ∀ n →
      Bishop.BishopEquivalent
        (natEmbed dataSet
          (n * Regroup.partitionCount n))
        (bishopFold
          (λ r →
            Bishop.bishopMul
              (natEmbed dataSet (Divisor.sigma1 r))
              (natEmbed dataSet (Regroup.partitionCount (n ∸ r))))
          (Hecke.oneTo n))

    -- Pointwise lower-grade majorants may be pushed through the finite
    -- sigma1 convolution.  This is the ordered-semiring/list-fold step.
    residualMajorantTransfer : ∀ n →
      (∀ r → r ∈ Hecke.oneTo n →
        Bishop.BishopLessEqual
          (natEmbed dataSet (Regroup.partitionCount (n ∸ r)))
          (exponentialMajorant dataSet (n ∸ r))) →
      Bishop.BishopLessEqual
        (bishopFold
          (λ r →
            Bishop.bishopMul
              (natEmbed dataSet (Divisor.sigma1 r))
              (natEmbed dataSet (Regroup.partitionCount (n ∸ r))))
          (Hecke.oneTo n))
        (weightedExponentialResidual dataSet n)

    -- This is the genuine Erdos analytic kernel inequality.  The historical
    -- proof derives it from sqrt concavity/tangent control, exponential laws,
    -- the degree-one weighted geometric estimate
    -- e^{-x}/(1-e^{-x})^2 < 1/x^2, and the Basel sum.
    erdosKernelEstimate : ∀ n →
      Bishop.BishopLessEqual
        (weightedExponentialResidual dataSet n)
        (Bishop.bishopMul
          (natEmbed dataSet n)
          (exponentialMajorant dataSet n))

    -- Cancellation by the positive embedded natural n.  This is separated
    -- explicitly from the kernel estimate so ordered-field plumbing cannot be
    -- confused with the source-specific analytic inequality.
    positiveNatScaleCancel : ∀ {n : Nat} →
      suc zero ≤ n →
      ∀ {left right : Bishop.Bishopℝ} →
      Bishop.BishopLessEqual
        (Bishop.bishopMul (natEmbed dataSet n) left)
        (Bishop.bishopMul (natEmbed dataSet n) right) →
      Bishop.BishopLessEqual left right

open ErdosBishopUpperMajorantAnalyticInputs public

------------------------------------------------------------------------
-- Exact dependency receipts: the analytic owner consumes the actual recurrence
-- already proved in the finite layer, not a separately postulated recurrence.

finiteRecurrenceReceipt :
  (n : Nat) →
  n * Regroup.partitionCount n ≡ Regroup.divisorSumRHS n
finiteRecurrenceReceipt = Recurrence.canonicalErdosDivisorSumRecurrence

finiteGeometricInfrastructureReceipt :
  GeometricBridge.ErdosWeightedGeometricFrontier
finiteGeometricInfrastructureReceipt =
  GeometricBridge.currentWeightedGeometricFrontier

------------------------------------------------------------------------
-- Source-route decomposition for the still-missing sharp kernel theorem.
-- Square-root *realization* now descends to rational approximation existence;
-- the tangent inequality and sharp kernel estimates remain analytic leaves.

data ErdosKernelProofRole : Set where
  bishopSquareRootApproximationExistence : ErdosKernelProofRole
  squareRootTangentInequality : ErdosKernelProofRole
  exponentialAdditivityAndMonotonicity : ErdosKernelProofRole
  degreeOneWeightedGeometricPointwiseDomination : ErdosKernelProofRole
  degreeOneWeightedGeometricReciprocalSquareBound : ErdosKernelProofRole
  baselSumPiSquaredOverSix : ErdosKernelProofRole
  constantPiSqrtTwoThirdsIdentification : ErdosKernelProofRole

------------------------------------------------------------------------
-- Boundary statement: the finite recurrence and coarse finite envelopes are
-- below this file; the sharp exp(c sqrt n) estimate begins here.
------------------------------------------------------------------------
