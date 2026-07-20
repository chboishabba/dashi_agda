module DASHI.Physics.YangMills.BalabanAnalyticProducerFrontier where

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanReferenceHodgeCoercivity as Hodge
import DASHI.Physics.YangMills.BalabanBackgroundPerturbationBudget as Perturbation
import DASHI.Physics.YangMills.BalabanCorrectionNeumannBound as Neumann
import DASHI.Physics.YangMills.BalabanSmallFieldNonlinearConstants as Nonlinear
import DASHI.Physics.YangMills.BalabanExplicitContractionBudget as Budget

record ProducerInputs (Index State Bound : Set) : Set₁ where
  field
    hodge : Hodge.ReferenceHodgeCoercivityData Index State Bound
    perturbation : Perturbation.BackgroundPerturbationComponents Index State Bound
    correction : Neumann.CorrectionNeumannData Index State Bound
    nonlinear : Nonlinear.SmallFieldNonlinearCoefficientData Bound
    budget : Budget.ExplicitContractionBudget Bound
    correctionMatches : Neumann.correctionUpper correction ≡ Budget.correctionUpper budget
    nonlinearMatches : Nonlinear.nonlinearUpper nonlinear ≡ Budget.nonlinearUpper budget

open ProducerInputs public

record ProducerCertificate (Index State Bound : Set) : Set₁ where
  field
    inputs : ProducerInputs Index State Bound
    referenceCoercive : ∀ index state → Hodge.LessEqual (hodge inputs) (Hodge.scale (hodge inputs) (Hodge.c0 (hodge inputs)) (Hodge.normSq (hodge inputs) index state)) (Hodge.referenceEnergy (hodge inputs) index state)
    perturbationBound : ∀ index state → Perturbation.LessEqual (perturbation inputs) (Perturbation.perturbationEnergy (perturbation inputs) index state) (Perturbation.scale (perturbation inputs) (Perturbation.perturbationUpper (perturbation inputs)) (Perturbation.normSq (perturbation inputs) index state))
    contraction : Budget.ContractionWitness (budget inputs)

assembleProducerCertificate : ∀ {Index State Bound : Set} → (inputs : ProducerInputs Index State Bound) → ProducerCertificate Index State Bound
assembleProducerCertificate inputs = record
  { inputs = inputs
  ; referenceCoercive = Hodge.referenceHessianCoercive (hodge inputs)
  ; perturbationBound = Perturbation.backgroundPerturbationBound (perturbation inputs)
  ; contraction = Budget.assembleContractionWitness (budget inputs)
  }

analyticProducerAssemblyLevel : ProofLevel
analyticProducerAssemblyLevel = machineChecked
analyticProducerEstimateInputsLevel : ProofLevel
analyticProducerEstimateInputsLevel = conditional
