module DASHI.Biology.OptogeneticMemoryObservationBoundaryExact where

-- Distinguishes optogenetic intervention, engram-associated neural activation,
-- behavioural readout, and claims about subjective experience.
--
-- Source provenance:
-- Liu et al. (2012), Optogenetic stimulation of a hippocampal engram
-- activates fear memory recall, Nature 484, 381-385.
-- DOI: 10.1038/nature11028.
-- Ramirez et al. (2013), Creating a false memory in the hippocampus,
-- Science 341, 387-391. DOI: 10.1126/science.1239073.
--
-- The map below is a typed abstraction; no behavioural causal effect sizes,
-- subjective phenomenology or full neural dynamics are derived here.

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)

record OptogeneticExperiment {ℓ : Level}
  (Light Neurons Behaviour : Set ℓ) : Set ℓ where
  field
    neuralResponse : Light → Neurons
    behaviouralReadout : Neurons → Behaviour
open OptogeneticExperiment public

predictedBehaviour :
  ∀ {ℓ} {L N B : Set ℓ} →
  OptogeneticExperiment L N B → L → B
predictedBehaviour e l =
  behaviouralReadout e (neuralResponse e l)

causalPipelineComposition :
  ∀ {ℓ} {L N B : Set ℓ}
  (e : OptogeneticExperiment L N B) (light : L) →
  predictedBehaviour e light ≡
  behaviouralReadout e (neuralResponse e light)
causalPipelineComposition e light = refl

-- Direct observation of behaviour does not supply an injective inverse from
-- Behaviour into phenomenal experience. No such function is exported.
record InterventionEvidence {ℓ : Level}
  {L N B : Set ℓ}
  (e : OptogeneticExperiment L N B) : Set (lsuc ℓ) where
  field
    observedBehaviour : L → B
    ProtocolAdequate : L → Set ℓ
    evidenceAgreement :
      (l : L) → ProtocolAdequate l →
      observedBehaviour l ≡ predictedBehaviour e l

-- Comparison point for measured neural magnetic activity; actual optical
-- perturbation artifacts and magnetic field inference require calibration.
