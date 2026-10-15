module DASHI.Physics.Foundations.FieldGeometryMatterExperimentParetoValidation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.FieldGeometryMatterExperimentParetoExact as Pareto

candidateCount : Nat
candidateCount = Pareto.candidateCount Pareto.canonicalExperimentPortfolio

candidateCountIsFive : candidateCount ≡ 5
candidateCountIsFive = refl

matbgSameSampleTargetExists : Pareto.ExperimentDomain
matbgSameSampleTargetExists = Pareto.matbgSameSampleSpectralEntropy

precisionReplicationTargetExists : Pareto.ExperimentDomain
precisionReplicationTargetExists = Pareto.precisionThrustIndependentReplication

quantumGravityTargetExists : Pareto.ExperimentDomain
quantumGravityTargetExists = Pareto.quantumStressGravityBackreaction

priorityDoesNotCreateTruth : Bool
priorityDoesNotCreateTruth =
  Pareto.priorityDoesNotCreateTruth Pareto.canonicalExperimentParetoBoundary

priorityDoesNotCreateAuthority : Bool
priorityDoesNotCreateAuthority =
  Pareto.priorityDoesNotCreateAuthority Pareto.canonicalExperimentParetoBoundary

externalExperimentStillRequired : Bool
externalExperimentStillRequired =
  Pareto.externalPaymentCannotBeReplacedByMoreFormalism
    Pareto.canonicalExperimentParetoBoundary
