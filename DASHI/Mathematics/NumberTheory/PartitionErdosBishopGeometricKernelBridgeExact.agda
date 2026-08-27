module DASHI.Mathematics.NumberTheory.PartitionErdosBishopGeometricKernelBridgeExact where

------------------------------------------------------------------------
-- CROSS-POLLINATION: ERDOS KERNEL <-> STEP-V GEOMETRIC INFRASTRUCTURE
--
-- P. Erdos (1942), DOI 10.2307/1968802, reduces the upper exponential bound
-- to a degree-one weighted geometric/exponential kernel.  The Yang--Mills Step
-- V lane already owns the relevant generic finite-series infrastructure over
-- Bishop reals.
--
-- Reuse that owner directly:
--
--   unweighted finite geometric supersolution      [machine checked]
--   polynomially weighted geometric interface      [available]
--   degree-one weighted realization                 [still to construct]
--
-- This module adds no new analytic axiom and no new real carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc; zero)

import Real as BishopReal

import DASHI.Physics.YangMills.BalabanStepVFiniteGeometricBackendExact as StepV
import DASHI.Physics.YangMills.BalabanStepVFiniteGeometricInductionExact as Induction
import DASHI.Physics.YangMills.BalabanStepVBishopFiniteGeometricExact as BishopGeometric
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- The exact ordered-semiring kernel is already instantiated on Bishop reals.

bishopKernel : StepV.OrderedSemiringKernel BishopReal.ℝ
bishopKernel = BishopGeometric.bishopOrderedSemiringKernel

bishopKernelLaws : Induction.GeometricSemiringLaws bishopKernel
bishopKernelLaws = BishopGeometric.bishopGeometricSemiringLaws

------------------------------------------------------------------------
-- Erdos needs the degree-one member of the generic polynomially weighted
-- geometric family: terms are schematically v*q^v.

ErdosDegreeOneWeightedGeometricBound : BishopReal.ℝ → Set₁
ErdosDegreeOneWeightedGeometricBound ratio =
  StepV.PolynomiallyWeightedGeometricBound bishopKernel ratio (suc zero)

------------------------------------------------------------------------
-- Existing unweighted geometric infrastructure is concrete and checked.

finiteBishopGeometricInfrastructureLevel : ProofLevel
finiteBishopGeometricInfrastructureLevel =
  BishopGeometric.bishopFiniteGeometricUniformBoundLevel

------------------------------------------------------------------------
-- The sharp Erdos kernel requires more than the unweighted sum.  The generic
-- degree-one interface exists, but an explicit Bishop inhabitant with the
-- reciprocal-square bound is not supplied here.

data ErdosWeightedGeometricFrontier : Set where
  degreeOneInterfaceAvailable : ErdosWeightedGeometricFrontier
  degreeOneBishopReciprocalSquareBoundPending : ErdosWeightedGeometricFrontier

currentWeightedGeometricFrontier : ErdosWeightedGeometricFrontier
currentWeightedGeometricFrontier =
  degreeOneBishopReciprocalSquareBoundPending

------------------------------------------------------------------------
-- This prevents a misleading boundary: the missing theorem is NOT generic
-- geometric convergence.  It is the quantitative degree-one weighted estimate
-- needed to match Erdos's reciprocal-square kernel.
------------------------------------------------------------------------
