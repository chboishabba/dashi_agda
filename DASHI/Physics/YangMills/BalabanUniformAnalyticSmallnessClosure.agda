module DASHI.Physics.YangMills.BalabanUniformAnalyticSmallnessClosure where

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanPatchRegimeHodgeUniformity as Hodge
import DASHI.Physics.YangMills.BalabanRadiusPerturbationSmallness as Perturbation
import DASHI.Physics.YangMills.BalabanPatchResidualSmallness as Residual
import DASHI.Physics.YangMills.BalabanCommonSmallFieldRadius as Radius
import DASHI.Physics.YangMills.BalabanExplicitContractionBudget as Contraction

------------------------------------------------------------------------
-- Coherent endpoint of the highest-alpha finite-volume smallness path.
------------------------------------------------------------------------

record UniformAnalyticSmallnessInputs
    (Index State Bound : Set) : Set₁ where
  field
    hodgeData : Hodge.PatchRegimeHodgeData Index State Bound
    perturbationData : Perturbation.RadiusPerturbationData Bound
    residualData : Residual.PatchResidualSmallnessData Bound
    radiusData : Radius.CommonSmallFieldRadiusData Bound
    contractionData : Contraction.ExplicitContractionBudget Bound

    radiusMatchesPerturbation :
      Radius.radius radiusData ≡ Perturbation.radius perturbationData
    residualQMatchesCorrectionBudget :
      Residual.q residualData ≡ Radius.neumannRadius radiusData
    contractionRhoMatchesRadiusBudget :
      Contraction.rhoG contractionData ≡ Radius.nonlinearRadius radiusData

open UniformAnalyticSmallnessInputs public

record UniformAnalyticSmallnessCertificate
    (Index State Bound : Set) : Set₁ where
  field
    inputs : UniformAnalyticSmallnessInputs Index State Bound
    uniformHodge : ∀ index state →
      Hodge.LessEqual (hodgeData inputs)
        (Hodge.scale (hodgeData inputs)
          (Hodge.commonConstant (hodgeData inputs))
          (Hodge.normSq (hodgeData inputs) index state))
        (Hodge.energy (hodgeData inputs) index state)
    coercivityBudget :
      Perturbation.LessEqual (perturbationData inputs)
        (Perturbation.add (perturbationData inputs)
          (Perturbation.cH (perturbationData inputs))
          (Perturbation.perturbationUpper (perturbationData inputs)))
        (Perturbation.c0 (perturbationData inputs))
    strictResidual : Residual.PatchResidualWitness (residualData inputs)
    commonRadius : Radius.CommonSmallFieldRadiusCertificate (radiusData inputs)
    strictContraction : Contraction.ContractionWitness (contractionData inputs)

open UniformAnalyticSmallnessCertificate public

assembleUniformAnalyticSmallness :
  ∀ {Index State Bound : Set} →
  (inputs : UniformAnalyticSmallnessInputs Index State Bound) →
  UniformAnalyticSmallnessCertificate Index State Bound
assembleUniformAnalyticSmallness inputs = record
  { inputs = inputs
  ; uniformHodge = Hodge.uniformPatchHodge (hodgeData inputs)
  ; coercivityBudget = Perturbation.fullCoercivityBudget (perturbationData inputs)
  ; strictResidual = Residual.assemblePatchResidualWitness (residualData inputs)
  ; commonRadius = Radius.assembleCommonSmallFieldRadius (radiusData inputs)
  ; strictContraction = Contraction.assembleContractionWitness (contractionData inputs)
  }

uniformAnalyticSmallnessAssemblyLevel : ProofLevel
uniformAnalyticSmallnessAssemblyLevel = machineChecked

uniformAnalyticSmallnessProducerInputsLevel : ProofLevel
uniformAnalyticSmallnessProducerInputsLevel = conditional
