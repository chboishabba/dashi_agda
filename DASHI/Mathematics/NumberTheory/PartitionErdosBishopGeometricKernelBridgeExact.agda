module DASHI.Mathematics.NumberTheory.PartitionErdosBishopGeometricKernelBridgeExact where

------------------------------------------------------------------------
-- CROSS-POLLINATION: ERDOS KERNEL <-> STEP-V GEOMETRIC INFRASTRUCTURE
--
-- P. Erdos (1942), DOI 10.2307/1968802, reduces the upper exponential bound
-- to a degree-one weighted geometric/exponential kernel.
--
-- The real carrier is the exact repository submodule at `vendor/bishop`.
--
-- The branch now owns two routes:
--
--   * the older generic Step-V polynomial-weighted domination adapter;
--   * a sharper direct finite route for q = exp(-x), 0 < x <= 1.
--
-- The direct route proves every cutoff sum W_N(q) is < 1/x^2 by combining an
-- exact finite weighted-geometric identity with concrete alternating-series
-- brackets for the Bishop exponential.  It does not require global exp-add.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (suc; zero)

import Real as BishopReal

import DASHI.Foundations.BishopVendoredSubmoduleProvenanceExact as Vendored
import DASHI.Foundations.BishopFiniteDegreeOneGeometricIdentityExact as DirectIdentity
import DASHI.Foundations.BishopNegativeExponentialFiniteDegreeOneKernelExact as DirectKernel
import DASHI.Foundations.BishopNegativeExponentialReciprocalSquareExact as Cross
import DASHI.Foundations.BishopNegativeExponentialReciprocalSquareDivisionExact as Division
import DASHI.Foundations.BishopNegativeExponentialUnitIntervalExact as Unit
import DASHI.Physics.YangMills.BalabanStepVFiniteGeometricBackendExact as StepV
import DASHI.Physics.YangMills.BalabanStepVFiniteGeometricInductionExact as Induction
import DASHI.Physics.YangMills.BalabanStepVBishopFiniteGeometricExact as BishopGeometric
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopDegreeOneDominationExact as DegreeOne
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- The exact ordered-semiring kernel is already instantiated on Bishop reals.

bishopKernel : StepV.OrderedSemiringKernel BishopReal.ℝ
bishopKernel = BishopGeometric.bishopOrderedSemiringKernel

bishopKernelLaws : Induction.GeometricSemiringLaws bishopKernel
bishopKernelLaws = BishopGeometric.bishopGeometricSemiringLaws

------------------------------------------------------------------------
-- Generic degree-one Step-V route retained for reuse.

ErdosDegreeOneWeightedGeometricBound : BishopReal.ℝ → Set₁
ErdosDegreeOneWeightedGeometricBound ratio =
  StepV.PolynomiallyWeightedGeometricBound bishopKernel ratio (suc zero)

ErdosDegreeOnePointwiseDomination : BishopReal.ℝ → Set₁
ErdosDegreeOnePointwiseDomination =
  DegreeOne.ErdosDegreeOnePointwiseDomination

pointwiseDominationClosesFiniteWeightedSum :
  ∀ {ratio : BishopReal.ℝ} →
  ErdosDegreeOnePointwiseDomination ratio →
  ErdosDegreeOneWeightedGeometricBound ratio
pointwiseDominationClosesFiniteWeightedSum =
  DegreeOne.erdosDegreeOneWeightedBound

------------------------------------------------------------------------
-- Sharper concrete exp(-x) route.

directFiniteErdosKernel :
  ∀ {x} →
  (inputs : Unit.PositiveUnitIntervalPoint x) →
  ∀ cutoff →
  BishopReal._<_
    (DirectIdentity.weightedPartial (Cross.q x) cutoff)
    (Division.inverseSquare x (Division.xNonzero inputs))
directFiniteErdosKernel inputs cutoff =
  DirectKernel.finiteNegativeExponentialDegreeOneKernel inputs cutoff

------------------------------------------------------------------------
-- Existing finite summation infrastructure is concrete and checked in its
-- pre-existing owners.  The direct negative-exponential tranche is source
-- implemented on this branch and remains pending the focused receipt.

finiteBishopGeometricInfrastructureLevel : ProofLevel
finiteBishopGeometricInfrastructureLevel =
  BishopGeometric.bishopFiniteGeometricUniformBoundLevel

degreeOneFiniteSummationLevel : ProofLevel
degreeOneFiniteSummationLevel =
  DegreeOne.erdosDegreeOneFiniteSummationLevel

------------------------------------------------------------------------
-- Sharpened frontier.

data ErdosWeightedGeometricFrontier : Set where
  unweightedBishopGeometricClosed : ErdosWeightedGeometricFrontier
  weightedFiniteSummationClosed : ErdosWeightedGeometricFrontier
  genericDegreeOnePointwiseDominationPending : ErdosWeightedGeometricFrontier
  directNegativeExponentialFiniteKernelImplemented : ErdosWeightedGeometricFrontier
  directNegativeExponentialFiniteKernelValidated : ErdosWeightedGeometricFrontier

currentWeightedGeometricFrontier : ErdosWeightedGeometricFrontier
currentWeightedGeometricFrontier =
  directNegativeExponentialFiniteKernelImplemented

------------------------------------------------------------------------
-- Current direct source theorem:
--
--   q = exp(-x), 0 < x <= 1
--
--   forall N,
--     sum_{v=1}^N v q^v < 1/x^2.
--
-- This bypasses the old generic pointwise-domination socket for the actual
-- Erdos ratio.  The remaining partition-specific weld is the exponential shift
-- comparison supplied by the square-root tangent estimate:
--
--   exp(c sqrt(n-r))
--     <= exp(c sqrt(n)) * exp(-r c/(2 sqrt(n))).
--
-- That is where the native Bishop Cauchy-product / exp-additivity theorem now
-- has highest alpha.
------------------------------------------------------------------------
