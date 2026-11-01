module DASHI.Mathematics.NumberTheory.PartitionErdosBishopDegreeOneDominationExact where

------------------------------------------------------------------------
-- ERDOS DEGREE-ONE KERNEL VIA EXISTING STEP-V DOMINATION
--
-- The Bishop carrier is supplied by the pinned `vendor/bishop` submodule;
-- see BishopVendoredSubmoduleProvenanceExact.  This module introduces no new
-- real implementation.
--
-- The generic Yang--Mills Step-V owner already proves:
--
--   pointwise polynomial/geometric domination
--     -> all finite weighted partial sums uniformly bounded.
--
-- Therefore the partition lane should not postulate an entire weighted-series
-- theorem.  It only needs to construct the degree-one pointwise domination
-- data for the ratio arising from exp(-x).
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)

import Real as BishopReal

import DASHI.Foundations.BishopVendoredSubmoduleProvenanceExact as Vendored
import DASHI.Physics.YangMills.BalabanStepVFiniteGeometricBackendExact as StepV
import DASHI.Physics.YangMills.BalabanStepVFiniteGeometricInductionExact as Geometric
import DASHI.Physics.YangMills.BalabanStepVBishopFiniteGeometricExact as BishopGeometric
import DASHI.Physics.YangMills.BalabanStepVPolynomialWeightedDominationExact as Weighted
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Concrete Bishop ordered-semiring backend inherited from vendor/bishop.

bishopKernel : StepV.OrderedSemiringKernel BishopReal.ℝ
bishopKernel = BishopGeometric.bishopOrderedSemiringKernel

bishopLaws : Geometric.GeometricSemiringLaws bishopKernel
bishopLaws = BishopGeometric.bishopGeometricSemiringLaws

degreeOne : Nat
degreeOne = suc zero

------------------------------------------------------------------------
-- The only domain-specific weighted-geometric input needed by the generic
-- summation theorem.

ErdosDegreeOnePointwiseDomination : BishopReal.ℝ → Set₁
ErdosDegreeOnePointwiseDomination ratio =
  Weighted.PolynomialGeometricDomination
    bishopKernel
    bishopLaws
    ratio
    degreeOne

------------------------------------------------------------------------
-- Generic Step-V machinery closes the entire finite summation layer once that
-- pointwise domination is supplied.

erdosDegreeOneWeightedBound :
  ∀ {ratio : BishopReal.ℝ} →
  ErdosDegreeOnePointwiseDomination ratio →
  StepV.PolynomiallyWeightedGeometricBound
    bishopKernel ratio degreeOne
erdosDegreeOneWeightedBound =
  Weighted.polynomiallyWeightedGeometricBoundFromDomination

erdosDegreeOneFiniteWeightedSumBound :
  ∀ {ratio : BishopReal.ℝ} →
  (inputs : ErdosDegreeOnePointwiseDomination ratio) →
  ∀ count →
  StepV.LessEqual bishopKernel
    (Weighted.weightedPartialSum
      bishopKernel
      (Weighted.weightedTerm inputs)
      count)
    (StepV.multiply bishopKernel
      (Weighted.dominationConstant inputs)
      (StepV.uniformBound (Weighted.largerRatioBound inputs)))
erdosDegreeOneFiniteWeightedSumBound inputs =
  Weighted.allFinitePolynomialWeightedSumsBounded inputs

------------------------------------------------------------------------
-- Status: finite summation is inherited from a machine-checked generic owner.
-- The remaining Erdos-specific analytic leaf is construction of the pointwise
-- domination itself (or a sharper direct reciprocal-square specialization).
------------------------------------------------------------------------

erdosDegreeOneFiniteSummationLevel : ProofLevel
erdosDegreeOneFiniteSummationLevel =
  Weighted.polynomialWeightedFiniteSummationLevel

erdosDegreeOnePointwiseDominationLevel : ProofLevel
erdosDegreeOnePointwiseDominationLevel = conditional
