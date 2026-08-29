module DASHI.Programmes.QuantumFalsifiableTargetExact where

open import DASHI.Core.Prelude
open import DASHI.Physics.Foundations.PhysicalTheoryExperimentDiscriminationExact

------------------------------------------------------------------------
-- dashiQ literal target/discrimination socket.
--
-- The repository explores emergent locality, Lorentz-invariance violation,
-- effective randomness, time asymmetry, and related projection hypotheses.
-- Those are research targets, not physical results.  A target becomes useful
-- to the formal programme when it is placed in an admissible experiment
-- language and actually separates candidate theories.
------------------------------------------------------------------------

data QuantumResearchTarget : Set where
  emergentLocality
  lorentzInvarianceViolation
  emergentRandomness
  projectionTimeAsymmetry
  lowEnergyRecovery : QuantumResearchTarget

record FalsifiableQuantumTarget
    (Theory Observation : Set) : Set₁ where
  constructor falsifiableQuantumTarget
  field
    language : Language QuantumResearchTarget
    predicts : Predictions Theory QuantumResearchTarget Observation
    target : QuantumResearchTarget
    leftCandidate rightCandidate : Theory
    targetIsAdmissibleExperiment : language target
    targetDiscriminatesCandidates :
      Discriminates predicts target leftCandidate rightCandidate

open FalsifiableQuantumTarget public

falsifiableTargetRefutesCurrentEquivalence :
  ∀ {Theory Observation : Set}
    (targetSocket : FalsifiableQuantumTarget Theory Observation) →
  ¬ (EquivalentOn
      (language targetSocket)
      (predicts targetSocket)
      (leftCandidate targetSocket)
      (rightCandidate targetSocket))
falsifiableTargetRefutesCurrentEquivalence targetSocket =
  includedDiscriminatorRefutesEquivalence
    (targetIsAdmissibleExperiment targetSocket)
    (targetDiscriminatesCandidates targetSocket)

------------------------------------------------------------------------
-- Physical promotion remains strictly stronger than possessing one useful
-- discriminator: GR/QFT recovery and the full promotion gate are still owned
-- by PhysicalTheoryExperimentDiscriminationExact.
------------------------------------------------------------------------

record QuantumTargetBoundary : Set where
  constructor quantumTargetBoundary
  field
    discriminatorAloneIsQuantumGravityTheory : Bool
    discriminatorAloneIsQuantumGravityTheoryIsFalse :
      discriminatorAloneIsQuantumGravityTheory ≡ false

    falsifiableTargetCanSplitCandidateClass : Bool
    falsifiableTargetCanSplitCandidateClassIsTrue :
      falsifiableTargetCanSplitCandidateClass ≡ true

canonicalQuantumTargetBoundary : QuantumTargetBoundary
canonicalQuantumTargetBoundary =
  quantumTargetBoundary
    false refl
    true refl
