module DASHI.Mathematics.NumberTheory.PartitionErdosBishopGeometricKernelBridgeExact where

------------------------------------------------------------------------
-- CROSS-POLLINATION: ERDOS KERNEL <-> STEP-V GEOMETRIC INFRASTRUCTURE
--
-- P. Erdos (1942), DOI 10.2307/1968802, reduces the upper exponential bound
-- to a degree-one weighted geometric/exponential kernel.
--
-- The real carrier is the exact repository submodule at `vendor/bishop`;
-- BishopVendoredSubmoduleProvenanceExact records the gitlink provenance.
--
-- Reuse already present on this branch:
--
--   unweighted finite Bishop geometric supersolution        [machine checked]
--   generic polynomial-weighted finite summation theorem    [machine checked]
--   degree-one adapter from pointwise domination            [implemented]
--
-- Therefore the missing Erdos theorem is no longer "construct a weighted
-- geometric series".  It is the specific pointwise/reciprocal-square estimate
-- linking the exp(-x) ratio to the sharp kernel used by the partition proof.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc; zero)

import Real as BishopReal

import DASHI.Foundations.BishopVendoredSubmoduleProvenanceExact as Vendored
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
-- Erdos needs the degree-one member of the generic polynomially weighted
-- geometric family: terms are schematically v*q^v.

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
-- Existing finite summation infrastructure is concrete and checked.

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
  degreeOnePointwiseDominationPending : ErdosWeightedGeometricFrontier
  degreeOneBishopReciprocalSquareBoundPending : ErdosWeightedGeometricFrontier

currentWeightedGeometricFrontier : ErdosWeightedGeometricFrontier
currentWeightedGeometricFrontier =
  degreeOnePointwiseDominationPending

------------------------------------------------------------------------
-- Source target for the eventual sharper specialization:
--
--   q = exp(-x), x > 0
--
--   sum_{v>=1} v q^v
--     = q / (1-q)^2
--     < 1/x^2.
--
-- The finite weighted-summation bureaucracy is already discharged by the
-- generic Step-V owner.  What remains is the concrete Bishop exponential /
-- inverse inequality (or an equivalent direct finite bound).
------------------------------------------------------------------------
