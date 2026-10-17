module DASHI.Physics.Chemistry.Nobel2026ChiralRecoverableObserverExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Core.EfficientRecoverableQuotientExact as Recoverable
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ObserverFactorizedRefinementExact as Factorized
import DASHI.Biology.CyclotomicPhaseAmplitudeBoundaryExact as C3
import DASHI.Physics.Chemistry.AsymmetricChiralDynamicsExact as Dynamics
import DASHI.Physics.Chemistry.CyclotomicChiralConjugationBridgeExact as ChiralC3

------------------------------------------------------------------------
-- CHIRAL PHASE AS A CONSUMER-RELATIVE RECOVERABLE QUOTIENT
--
-- Cross-pollination with the Eisenstein observer work in PR #1145 sharpens the
-- chemistry result.  The phase observer forgets seed-vs-amplified magnitude,
-- but that loss is consumer-relative: it is sufficient for handed branch and
-- insufficient for full state identity.  Phase + magnitude residual reopens
-- the complete five-state finite chemistry fixture exactly.
------------------------------------------------------------------------

reopenChiralState : C3.C3Phase → Nat → Dynamics.ChiralBiasState
reopenChiralState C3.phaseOne magnitude = Dynamics.racemic
reopenChiralState C3.phaseZeta zero = Dynamics.leftAmplified
reopenChiralState C3.phaseZeta (suc zero) = Dynamics.leftSeed
reopenChiralState C3.phaseZeta (suc (suc magnitude)) = Dynamics.leftAmplified
reopenChiralState C3.phaseZetaSquared zero = Dynamics.rightAmplified
reopenChiralState C3.phaseZetaSquared (suc zero) = Dynamics.rightSeed
reopenChiralState C3.phaseZetaSquared (suc (suc magnitude)) = Dynamics.rightAmplified

phaseMagnitudeReopensState :
  (x : Dynamics.ChiralBiasState) →
  reopenChiralState (ChiralC3.chiralPhase x) (Dynamics.biasMagnitudeCode x) ≡ x
phaseMagnitudeReopensState Dynamics.leftAmplified = refl
phaseMagnitudeReopensState Dynamics.leftSeed = refl
phaseMagnitudeReopensState Dynamics.racemic = refl
phaseMagnitudeReopensState Dynamics.rightSeed = refl
phaseMagnitudeReopensState Dynamics.rightAmplified = refl

chiralIdentityWitnessProblem : Recoverable.WitnessProblem
chiralIdentityWitnessProblem =
  Recoverable.witnessProblem
    Dynamics.ChiralBiasState
    Dynamics.ChiralBiasState
    (λ instance witness → witness ≡ instance)

chiralPhaseMagnitudeRecoverableQuotient :
  Recoverable.WitnessRecoverableQuotient chiralIdentityWitnessProblem
chiralPhaseMagnitudeRecoverableQuotient =
  Recoverable.witnessRecoverableQuotient
    C3.C3Phase
    Nat
    ChiralC3.chiralPhase
    Dynamics.biasMagnitudeCode
    reopenChiralState
    phaseMagnitudeReopensState

------------------------------------------------------------------------
-- Phase is deliberately lossy for the identity consumer.
------------------------------------------------------------------------

identityConsumer : Dynamics.ChiralBiasState → Dynamics.ChiralBiasState
identityConsumer x = x

leftPhaseCollision :
  ChiralC3.chiralPhase Dynamics.leftSeed
  ≡ ChiralC3.chiralPhase Dynamics.leftAmplified
leftPhaseCollision = refl

leftSeedNotAmplified : Dynamics.leftSeed ≡ Dynamics.leftAmplified → ⊥
leftSeedNotAmplified ()

phaseIdentityNonDescent :
  Descent.ConsumerNonDescentWitness ChiralC3.chiralPhase identityConsumer
phaseIdentityNonDescent =
  Descent.consumerNonDescentWitness
    Dynamics.leftSeed
    Dynamics.leftAmplified
    leftPhaseCollision
    leftSeedNotAmplified

phaseCannotPayIdentityConsumer :
  Descent.ConsumerSufficient ChiralC3.chiralPhase identityConsumer → ⊥
phaseCannotPayIdentityConsumer =
  Descent.nonDescentWitnessBlocksSufficiency phaseIdentityNonDescent

------------------------------------------------------------------------
-- The same phase observer is exactly sufficient for the handed-branch
-- consumer.  This is the chemistry analogue of PR #1145's result that one C3
-- observer may be insufficient for identity yet sufficient for chi_-3.
------------------------------------------------------------------------

branchOfPhase : C3.C3Phase → Dynamics.FutureBranchReadout
branchOfPhase C3.phaseOne = Dynamics.futureRacemic
branchOfPhase C3.phaseZeta = Dynamics.futureLeft
branchOfPhase C3.phaseZetaSquared = Dynamics.futureRight

futureBranchFactorsThroughPhase :
  Descent.FactorsThrough ChiralC3.chiralPhase Dynamics.futureBranch
futureBranchFactorsThroughPhase =
  Factorized.factorizedRefinement
    branchOfPhase
    factorLaw
  where
    factorLaw :
      (x : Dynamics.ChiralBiasState) →
      Dynamics.futureBranch x ≡ branchOfPhase (ChiralC3.chiralPhase x)
    factorLaw Dynamics.leftAmplified = refl
    factorLaw Dynamics.leftSeed = refl
    factorLaw Dynamics.racemic = refl
    factorLaw Dynamics.rightSeed = refl
    factorLaw Dynamics.rightAmplified = refl

phaseIsSufficientForFutureBranch :
  Descent.ConsumerSufficient ChiralC3.chiralPhase Dynamics.futureBranch
phaseIsSufficientForFutureBranch =
  Descent.fibreConstantIsConsumerSufficient
    (Descent.factorsThroughImpliesFibreConstant futureBranchFactorsThroughPhase)

futureBranchObserverIsLeastSufficient :
  Descent.LeastSufficientConsumerObserver Dynamics.futureBranch
futureBranchObserverIsLeastSufficient =
  Descent.canonicalConsumerObserverIsLeast Dynamics.futureBranch

record ChiralRecoverableObserverBoundary : Set where
  constructor chiralRecoverableObserverBoundary
  field
    phaseAloneRecoversFullState : Bool
    phasePlusMagnitudeReopensFullState : Bool
    phaseSufficientForHandedBranch : Bool
    phaseSufficientForIdentity : Bool
    consumerRelativeLossPaid : Bool
    recoverableResidualIsNewPhysicalMechanism : Bool

canonicalChiralRecoverableObserverBoundary : ChiralRecoverableObserverBoundary
canonicalChiralRecoverableObserverBoundary =
  chiralRecoverableObserverBoundary
    false true true false true false
