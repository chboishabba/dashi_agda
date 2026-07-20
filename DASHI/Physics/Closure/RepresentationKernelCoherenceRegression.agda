module DASHI.Physics.Closure.RepresentationKernelCoherenceRegression where

-- Compact import and witness surface for the representation/kernel tranche.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Unit using (⊤; tt)

import DASHI.Physics.Closure.RepresentationKernelCompatibility as RKC
import DASHI.Physics.Closure.RepresentationKernelRefinementBridge as RefinementBridge
import DASHI.Physics.Closure.RepresentationAttractorTransport as Attractor
import DASHI.Physics.Closure.ScheduleRepresentationCoherence as Schedule
import DASHI.Physics.Closure.TwoChannelTransportRepresentationWitness as Transport

transportOneStepRegression :
  ∀ x →
  Transport.projectTransport (Transport.fineTransportStep x)
  ≡
  Transport.coarseTransportStep (Transport.projectTransport x)
transportOneStepRegression x =
  Transport.transportProjectionCommutes tt

transportTrajectoryRegression :
  ∀ x n →
  Transport.projectTransport
    (RKC.iterate Transport.fineTransportStep n x)
  ≡
  RKC.iterate Transport.coarseTransportStep n
    (Transport.projectTransport x)
transportTrajectoryRegression = Transport.transportTrajectoryCommutes

transportApproximateDefectIsZero :
  ∀ n x →
  RKC.ApproxRepresentationKernelCompatibility.trajectoryDefect
    Transport.transportApproxRepresentationLaw n x
  ≡ 0
transportApproximateDefectIsZero _ _ = refl

representationKernelCoherenceRegressionEvidence : Set
representationKernelCoherenceRegressionEvidence = ⊤

representationKernelCoherenceRegressionWitness :
  representationKernelCoherenceRegressionEvidence
representationKernelCoherenceRegressionWitness = tt
