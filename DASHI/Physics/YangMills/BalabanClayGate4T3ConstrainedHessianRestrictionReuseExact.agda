module DASHI.Physics.YangMills.BalabanClayGate4T3ConstrainedHessianRestrictionReuseExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT3PhysicalUniformFluctuationCoercivityExact as T3
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedMinimizerProjectionExact as Minimizer
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedHessianRestrictionExact as Restriction

------------------------------------------------------------------------
-- Primary provenance.
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
-- This module attaches the new constrained restriction algebra directly to the
-- existing T3 physical/reference Hessian and five-channel remainder owner.
-- T3's epsilonTotal is a relative quadratic-form budget. It is not silently
-- converted into the operator norm required by the determinant theorem.
------------------------------------------------------------------------

record T3ConstrainedRestrictionInputs
    (Scale Volume PatchRegime Background Fluctuation Tangent Bound Coarse : Set)
    : Set₁ where
  field
    t3 : T3.SmallFieldFluctuationCoercivityData
      Scale Volume PatchRegime Background Fluctuation Tangent Bound

    minimizerData : Scale → Volume → PatchRegime → Background →
      Minimizer.ConstrainedMinimizerData Fluctuation Coarse

    projection projectionAdjoint :
      Scale → Volume → PatchRegime → Background →
      Fluctuation → Fluctuation

    projectionAdjointAdd : ∀ scale volume regime background left right →
      projectionAdjoint scale volume regime background
        (T3.addFluctuation t3 left right)
      ≡ T3.addFluctuation t3
          (projectionAdjoint scale volume regime background left)
          (projectionAdjoint scale volume regime background right)

    ProjectionMatchesMinimizerKernel :
      Scale → Volume → PatchRegime → Background → Set

    projectionMatchesMinimizerKernel : ∀ scale volume regime background →
      ProjectionMatchesMinimizerKernel scale volume regime background

open T3ConstrainedRestrictionInputs public

restrictionAt :
  ∀ {Scale Volume PatchRegime Background Fluctuation Tangent Bound Coarse : Set}
    (inputs : T3ConstrainedRestrictionInputs
      Scale Volume PatchRegime Background Fluctuation Tangent Bound Coarse)
    scale volume regime background →
  Restriction.ConstrainedHessianRestrictionData Fluctuation
restrictionAt inputs scale volume regime background = record
  { projection = projection inputs scale volume regime background
  ; projectionAdjoint =
      projectionAdjoint inputs scale volume regime background
  ; referenceHessian =
      T3.referenceHessian (t3 inputs)
        (T3.makeIndex (t3 inputs) scale volume regime background)
  ; physicalHessian =
      T3.physicalFluctuationHessian (t3 inputs)
        scale volume regime background
  ; perturbationHessian =
      T3.backgroundHessianRemainder (t3 inputs)
        (T3.makeIndex (t3 inputs) scale volume regime background)
  ; add = T3.addFluctuation (t3 inputs)
  ; physicalHessianSplits =
      T3.physicalFluctuationHessianSplit (t3 inputs)
        scale volume regime background
  ; projectionAdjointAdd =
      projectionAdjointAdd inputs scale volume regime background
  }

restrictedT3PhysicalHessianSplitsExactly :
  ∀ {Scale Volume PatchRegime Background Fluctuation Tangent Bound Coarse : Set}
    (inputs : T3ConstrainedRestrictionInputs
      Scale Volume PatchRegime Background Fluctuation Tangent Bound Coarse)
    scale volume regime background fluctuation →
  Restriction.restrictedPhysicalHessian
    (restrictionAt inputs scale volume regime background) fluctuation
  ≡ T3.addFluctuation (t3 inputs)
      (Restriction.restrictedReferenceHessian
        (restrictionAt inputs scale volume regime background) fluctuation)
      (Restriction.restrictedPerturbationHessian
        (restrictionAt inputs scale volume regime background) fluctuation)
restrictedT3PhysicalHessianSplitsExactly inputs scale volume regime background =
  Restriction.restrictedPhysicalSplitsExactly
    (restrictionAt inputs scale volume regime background)

record T3RestrictedOperatorNormInputs
    {Scale Volume PatchRegime Background Fluctuation Tangent Bound Coarse : Set}
    (inputs : T3ConstrainedRestrictionInputs
      Scale Volume PatchRegime Background Fluctuation Tangent Bound Coarse)
    (scale : Scale) (volume : Volume)
    (regime : PatchRegime) (background : Background) : Set₁ where
  field
    ambientRemainderNorm restrictedRemainderNorm epsilonOperator : Bound

    lessEqualTransitive : ∀ {left middle right} →
      T3.LessEqual (t3 inputs) left middle →
      T3.LessEqual (t3 inputs) middle right →
      T3.LessEqual (t3 inputs) left right

    projectionDoesNotIncreaseRemainderNorm :
      T3.LessEqual (t3 inputs)
        restrictedRemainderNorm ambientRemainderNorm

    ambientRemainderOperatorNormBound :
      T3.LessEqual (t3 inputs)
        ambientRemainderNorm epsilonOperator

open T3RestrictedOperatorNormInputs public

toProjectedPerturbationNormData :
  ∀ {Scale Volume PatchRegime Background Fluctuation Tangent Bound Coarse : Set}
    {inputs : T3ConstrainedRestrictionInputs
      Scale Volume PatchRegime Background Fluctuation Tangent Bound Coarse}
    {scale : Scale} {volume : Volume}
    {regime : PatchRegime} {background : Background} →
  T3RestrictedOperatorNormInputs inputs scale volume regime background →
  Restriction.ProjectedPerturbationNormData Bound
toProjectedPerturbationNormData {inputs = inputs} normInputs = record
  { ambientPerturbationNorm = ambientRemainderNorm normInputs
  ; restrictedPerturbationNorm = restrictedRemainderNorm normInputs
  ; epsilon = epsilonOperator normInputs
  ; LessEqual = T3.LessEqual (t3 inputs)
  ; transitive = lessEqualTransitive normInputs
  ; projectionDoesNotIncreasePerturbationNorm =
      projectionDoesNotIncreaseRemainderNorm normInputs
  ; ambientPerturbationBelowEpsilon =
      ambientRemainderOperatorNormBound normInputs
  }

restrictedT3RemainderBelowOperatorEpsilon :
  ∀ {Scale Volume PatchRegime Background Fluctuation Tangent Bound Coarse : Set}
    {inputs : T3ConstrainedRestrictionInputs
      Scale Volume PatchRegime Background Fluctuation Tangent Bound Coarse}
    {scale : Scale} {volume : Volume}
    {regime : PatchRegime} {background : Background}
    (normInputs : T3RestrictedOperatorNormInputs
      inputs scale volume regime background) →
  T3.LessEqual (t3 inputs)
    (restrictedRemainderNorm normInputs)
    (epsilonOperator normInputs)
restrictedT3RemainderBelowOperatorEpsilon normInputs =
  Restriction.restrictedPerturbationBelowEpsilon
    (toProjectedPerturbationNormData normInputs)

t3PhysicalHessianRestrictionReuseLevel : ProofLevel
t3PhysicalHessianRestrictionReuseLevel = machineChecked

t3RestrictedHessianSplitLevel : ProofLevel
t3RestrictedHessianSplitLevel = machineChecked

t3ProjectedOperatorNormTransportLevel : ProofLevel
t3ProjectedOperatorNormTransportLevel = machineChecked

physicalT3ProjectionMeaningInputsLevel : ProofLevel
physicalT3ProjectionMeaningInputsLevel = conditional

physicalT3AmbientRemainderOperatorNormInputsLevel : ProofLevel
physicalT3AmbientRemainderOperatorNormInputsLevel = conditional

relativeFormBudgetToOperatorNormAcceptedWithoutProof : ProofLevel
relativeFormBudgetToOperatorNormAcceptedWithoutProof = conjectural
