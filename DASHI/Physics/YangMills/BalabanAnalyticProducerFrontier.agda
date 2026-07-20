module DASHI.Physics.YangMills.BalabanAnalyticProducerFrontier where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanReferenceHodgeCoercivity as Hodge
import DASHI.Physics.YangMills.BalabanBackgroundPerturbationBudget as Perturbation
import DASHI.Physics.YangMills.BalabanCorrectionNeumannBound as Neumann
import DASHI.Physics.YangMills.BalabanSmallFieldNonlinearConstants as Nonlinear
import DASHI.Physics.YangMills.BalabanExplicitContractionBudget as Budget

------------------------------------------------------------------------
-- Exact remaining producer boundary for an unconditional finite-volume
-- background theorem.  Every broad B1/B3/B5/B7 field now factors through one of
-- the smaller data packages below.
------------------------------------------------------------------------

record BackgroundAnalyticProducerInputs
    (Index State Bound : Set) : Set₁ where
  field
    referenceHodge : Hodge.ReferenceHodgeCoercivityData Index State Bound
    perturbationComponents :
      Perturbation.BackgroundPerturbationComponents Index State Bound
    correctionNeumann : Neumann.CorrectionNeumannData Index State Bound
    nonlinearCoefficients : Nonlinear.SmallFieldNonlinearCoefficientData Bound
    contractionBudget : Budget.ExplicitContractionBudget Bound

    referenceConstantMatches :
      Hodge.c0 referenceHodge ≡ Hodge.hodgeConstant referenceHodge

    perturbationConstantMatches :
      Perturbation.perturbationUpper perturbationComponents ≡
      Perturbation.perturbationUpper perturbationComponents

    correctionConstantMatches :
      Neumann.correctionUpper correctionNeumann ≡
      Budget.correctionUpper contractionBudget

    nonlinearConstantMatches :
      Nonlinear.nonlinearUpper nonlinearCoefficients ≡
      Budget.nonlinearUpper contractionBudget

open BackgroundAnalyticProducerInputs public

record BackgroundAnalyticProducerCertificates
    (Index State Bound : Set) : Set₁ where
  field
    inputs : BackgroundAnalyticProducerInputs Index State Bound

    referenceCoercivity : ∀ index state →
      Hodge.LessEqual (referenceHodge inputs)
        (Hodge.scale (referenceHodge inputs)
          (Hodge.c0 (referenceHodge inputs))
          (Hodge.normSq (referenceHodge inputs) index state))
        (Hodge.referenceEnergy (referenceHodge inputs) index state)

    perturbationBound : ∀ index state →
      Perturbation.LessEqual (perturbationComponents inputs)
        (Perturbation.perturbationEnergy (perturbationComponents inputs)
          index state)
        (Perturbation.scale (perturbationComponents inputs)
          (Perturbation.perturbationUpper (perturbationComponents inputs))
          (Perturbation.normSq (perturbationComponents inputs) index state))

    strictContraction : Budget.ContractionWitness (contractionBudget inputs)

open BackgroundAnalyticProducerCertificates public

assembleBackgroundAnalyticProducerCertificates :
  ∀ {Index State Bound : Set} →
  (inputs : BackgroundAnalyticProducerInputs Index State Bound) →
  BackgroundAnalyticProducerCertificates Index State Bound
assembleBackgroundAnalyticProducerCertificates inputs = record
  { inputs = inputs
  ; referenceCoercivity = Hodge.referenceHessianCoercive (referenceHodge inputs)
  ; perturbationBound =
      Perturbation.backgroundPerturbationBound (perturbationComponents inputs)
  ; strictContraction = Budget.assembleContractionWitness (contractionBudget inputs)
  }

analyticProducerAssemblyLevel : ProofLevel
analyticProducerAssemblyLevel = machineChecked

analyticProducerEstimateInputsLevel : ProofLevel
analyticProducerEstimateInputsLevel = conditional
