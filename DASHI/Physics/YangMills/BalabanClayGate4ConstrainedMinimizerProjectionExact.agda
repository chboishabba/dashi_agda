module DASHI.Physics.YangMills.BalabanClayGate4ConstrainedMinimizerProjectionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Primary and secondary provenance.
--
-- Tadeusz Balaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge Field
-- Theories I", Communications in Mathematical Physics 95 (1984), 17--40.
-- DOI: 10.1007/BF01215757.
--
-- Tadeusz Balaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01215910.
--
-- Abhishek Goswami,
-- "The Variational Problem and Background Field in the Renormalization Group
-- Method for Non-Linear Sigma Models", Annales Henri Poincare 25 (2024).
-- DOI: 10.1007/s00023-023-01353-7; arXiv:2204.08252.
--
-- Goswami's equations (35)--(38) restate the constrained linear variational
-- problem and the minimizer formula used in Balaban's programme:
--
--   H B = G Q* (Q G Q*)^{-1} B.
--
-- Equations (88)--(93) likewise use P = I - H Q as the projection onto the
-- tangent subspace Q A = 0. The algebra below is independent of the analytic
-- construction of G and of the physical Hessian; those remain explicit inputs.
------------------------------------------------------------------------

record ConstrainedMinimizerData (Fine Coarse : Set) : Set₁ where
  field
    blockMap : Fine → Coarse
    green : Fine → Fine
    blockAdjoint : Coarse → Fine
    coarseGramInverse : Coarse → Coarse

    coarseGramRightInverse : ∀ (coarse : Coarse) →
      blockMap (green (blockAdjoint (coarseGramInverse coarse)))
      ≡ coarse

open ConstrainedMinimizerData public

constrainedMinimizer :
  ∀ {Fine Coarse : Set} →
  ConstrainedMinimizerData Fine Coarse → Coarse → Fine
constrainedMinimizer dataSet coarse =
  green dataSet (blockAdjoint dataSet (coarseGramInverse dataSet coarse))

constrainedMinimizerSatisfiesConstraint :
  ∀ {Fine Coarse : Set}
    (dataSet : ConstrainedMinimizerData Fine Coarse)
    (coarse : Coarse) →
  blockMap dataSet (constrainedMinimizer dataSet coarse) ≡ coarse
constrainedMinimizerSatisfiesConstraint dataSet =
  coarseGramRightInverse dataSet

record ConstraintProjectionAlgebra
    {Fine Coarse : Set}
    (dataSet : ConstrainedMinimizerData Fine Coarse) : Set₁ where
  field
    subtractFine : Fine → Fine → Fine
    subtractCoarse : Coarse → Coarse → Coarse
    zeroCoarse : Coarse

    blockMapSubtract : ∀ (left right : Fine) →
      blockMap dataSet (subtractFine left right)
      ≡ subtractCoarse (blockMap dataSet left) (blockMap dataSet right)

    subtractSelf : ∀ (coarse : Coarse) →
      subtractCoarse coarse coarse ≡ zeroCoarse

open ConstraintProjectionAlgebra public

constraintProjection :
  ∀ {Fine Coarse : Set}
    {dataSet : ConstrainedMinimizerData Fine Coarse} →
  ConstraintProjectionAlgebra dataSet → Fine → Fine
constraintProjection {dataSet = dataSet} algebra fine =
  subtractFine algebra fine
    (constrainedMinimizer dataSet (blockMap dataSet fine))

constraintProjectionLiesInKernel :
  ∀ {Fine Coarse : Set}
    {dataSet : ConstrainedMinimizerData Fine Coarse}
    (algebra : ConstraintProjectionAlgebra dataSet)
    (fine : Fine) →
  blockMap dataSet (constraintProjection algebra fine)
  ≡ zeroCoarse algebra
constraintProjectionLiesInKernel {dataSet = dataSet} algebra fine =
  trans
    (blockMapSubtract algebra fine
      (constrainedMinimizer dataSet (blockMap dataSet fine)))
    (trans
      (cong₂ (subtractCoarse algebra)
        refl
        (constrainedMinimizerSatisfiesConstraint dataSet
          (blockMap dataSet fine)))
      (subtractSelf algebra (blockMap dataSet fine)))

record PhysicalConstrainedHessianMeaning
    (Scale Background Fine Coarse Matrix : Set) : Set₁ where
  field
    minimizerData : Scale → Background →
      ConstrainedMinimizerData Fine Coarse

    constrainedTangentProjection : Scale → Background → Fine → Fine
    finiteReferenceHessian finitePhysicalHessian :
      Scale → Background → Matrix

    projectionMeaning : ∀ (scale : Scale) (background : Background) →
      Set
    referenceHessianMeaning : ∀ (scale : Scale) (background : Background) →
      Set
    physicalHessianMeaning : ∀ (scale : Scale) (background : Background) →
      Set

open PhysicalConstrainedHessianMeaning public

constrainedMinimizerFormulaLevel : ProofLevel
constrainedMinimizerFormulaLevel = machineChecked

constraintProjectionKernelLevel : ProofLevel
constraintProjectionKernelLevel = machineChecked

balabanMinimizerProvenanceLevel : ProofLevel
balabanMinimizerProvenanceLevel = standardImported

physicalConstraintProjectionMeaningInputsLevel : ProofLevel
physicalConstraintProjectionMeaningInputsLevel = conditional

physicalConstrainedFiniteHessianMeaningInputsLevel : ProofLevel
physicalConstrainedFiniteHessianMeaningInputsLevel = conditional
