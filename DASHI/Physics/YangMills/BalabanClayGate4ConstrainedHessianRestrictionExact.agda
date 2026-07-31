module DASHI.Physics.YangMills.BalabanClayGate4ConstrainedHessianRestrictionExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedMinimizerProjectionExact as Minimizer

------------------------------------------------------------------------
-- Constrained Hessian restriction algebra.
--
-- Primary provenance for the background-field and constrained propagator
-- architecture:
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- This module proves only the exact linear algebra.  It does not identify the
-- physical second variation or prove its uniform analytic perturbation bound.
------------------------------------------------------------------------

record ConstrainedHessianRestrictionData (Fine : Set) : Set₁ where
  field
    projection projectionAdjoint : Fine → Fine

    referenceHessian physicalHessian perturbationHessian : Fine → Fine
    add : Fine → Fine → Fine

    physicalHessianSplits : ∀ fine →
      physicalHessian fine
      ≡ add (referenceHessian fine) (perturbationHessian fine)

    projectionAdjointAdd : ∀ left right →
      projectionAdjoint (add left right)
      ≡ add (projectionAdjoint left) (projectionAdjoint right)

open ConstrainedHessianRestrictionData public

restrictedReferenceHessian :
  ∀ {Fine : Set} →
  ConstrainedHessianRestrictionData Fine → Fine → Fine
restrictedReferenceHessian dataSet fine =
  projectionAdjoint dataSet
    (referenceHessian dataSet (projection dataSet fine))

restrictedPhysicalHessian :
  ∀ {Fine : Set} →
  ConstrainedHessianRestrictionData Fine → Fine → Fine
restrictedPhysicalHessian dataSet fine =
  projectionAdjoint dataSet
    (physicalHessian dataSet (projection dataSet fine))

restrictedPerturbationHessian :
  ∀ {Fine : Set} →
  ConstrainedHessianRestrictionData Fine → Fine → Fine
restrictedPerturbationHessian dataSet fine =
  projectionAdjoint dataSet
    (perturbationHessian dataSet (projection dataSet fine))

restrictedPhysicalSplitsExactly :
  ∀ {Fine : Set}
    (dataSet : ConstrainedHessianRestrictionData Fine)
    fine →
  restrictedPhysicalHessian dataSet fine
  ≡ add dataSet
      (restrictedReferenceHessian dataSet fine)
      (restrictedPerturbationHessian dataSet fine)
restrictedPhysicalSplitsExactly dataSet fine =
  trans
    (cong (projectionAdjoint dataSet)
      (physicalHessianSplits dataSet (projection dataSet fine)))
    (projectionAdjointAdd dataSet
      (referenceHessian dataSet (projection dataSet fine))
      (perturbationHessian dataSet (projection dataSet fine)))

record ProjectedPerturbationNormData (Bound : Set) : Set₁ where
  field
    ambientPerturbationNorm restrictedPerturbationNorm epsilon : Bound
    LessEqual : Bound → Bound → Set

    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    projectionDoesNotIncreasePerturbationNorm :
      LessEqual restrictedPerturbationNorm ambientPerturbationNorm

    ambientPerturbationBelowEpsilon :
      LessEqual ambientPerturbationNorm epsilon

open ProjectedPerturbationNormData public

restrictedPerturbationBelowEpsilon :
  ∀ {Bound : Set}
    (dataSet : ProjectedPerturbationNormData Bound) →
  LessEqual dataSet
    (restrictedPerturbationNorm dataSet)
    (epsilon dataSet)
restrictedPerturbationBelowEpsilon dataSet =
  transitive dataSet
    (projectionDoesNotIncreasePerturbationNorm dataSet)
    (ambientPerturbationBelowEpsilon dataSet)

record PhysicalConstrainedHessianRestrictionMeaning
    (Scale Background Fine Coarse : Set) : Set₁ where
  field
    minimizer : Scale → Background →
      Minimizer.ConstrainedMinimizerData Fine Coarse

    restriction : Scale → Background →
      ConstrainedHessianRestrictionData Fine

    projectionIsMinimizerKernelProjection : ∀ scale background →
      Set

    physicalSecondVariationMeaning : ∀ scale background → Set
    referenceSecondVariationMeaning : ∀ scale background → Set
    perturbationDifferenceMeaning : ∀ scale background → Set

open PhysicalConstrainedHessianRestrictionMeaning public

constrainedHessianRestrictionSplitLevel : ProofLevel
constrainedHessianRestrictionSplitLevel = machineChecked

projectedPerturbationNormTransportLevel : ProofLevel
projectedPerturbationNormTransportLevel = machineChecked

physicalProjectionAdjointMeaningInputsLevel : ProofLevel
physicalProjectionAdjointMeaningInputsLevel = conditional

physicalHessianSecondVariationSplitInputsLevel : ProofLevel
physicalHessianSecondVariationSplitInputsLevel = conditional

physicalAmbientHessianPerturbationBoundInputsLevel : ProofLevel
physicalAmbientHessianPerturbationBoundInputsLevel = conditional
