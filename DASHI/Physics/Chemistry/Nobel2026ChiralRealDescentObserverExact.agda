module DASHI.Physics.Chemistry.Nobel2026ChiralRealDescentObserverExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ObserverFactorizedRefinementExact as Factorized
import DASHI.Moonshine.C3CyclotomicRealDescentExact as RealDescent
import DASHI.Physics.Chemistry.AsymmetricChiralDynamicsExact as Dynamics
import DASHI.Physics.Chemistry.CyclotomicChiralConjugationBridgeExact as ChiralC3
import DASHI.Physics.Chemistry.Nobel2026CyclotomicCarrierEquivalenceExact as Carrier
import DASHI.Physics.Chemistry.Nobel2026ChiralRecoverableObserverExact as Recoverable

------------------------------------------------------------------------
-- FIXED-PLUS-CONJUGATE-PAIR DESCENT AS AN OBSERVER HIERARCHY
--
-- The merged C3 real-descent owner has one fixed real axis and one transverse
-- conjugate plane.  Pulling that structure back through the chemistry phase
-- observer gives an exact hierarchy:
--
--   full five-state chiral fixture
--       -> C3 phase: racemic / left / right
--       -> realified sector: fixed / nontrivial-conjugate-pair
--       -> one-point chemistry chart.
--
-- Each quotient is judged only against a declared consumer.  In particular,
-- realification can answer racemic-vs-nonracemic but cannot recover handedness.
------------------------------------------------------------------------

realifiedChiralObserver : Dynamics.ChiralBiasState → RealDescent.RealifiedC3Sector
realifiedChiralObserver x =
  Carrier.chemRealifiedSector (ChiralC3.chiralPhase x)

racemicDescendsToFixedAxis :
  realifiedChiralObserver Dynamics.racemic ≡ RealDescent.fixedRealAxis
racemicDescendsToFixedAxis = refl

leftSeedDescendsToTransversePlane :
  realifiedChiralObserver Dynamics.leftSeed ≡ RealDescent.transverseConjugatePlane
leftSeedDescendsToTransversePlane = refl

rightSeedDescendsToTransversePlane :
  realifiedChiralObserver Dynamics.rightSeed ≡ RealDescent.transverseConjugatePlane
rightSeedDescendsToTransversePlane = refl

leftRightRealifiedCollision :
  realifiedChiralObserver Dynamics.leftSeed
  ≡ realifiedChiralObserver Dynamics.rightSeed
leftRightRealifiedCollision = refl

realifiedFutureBranchNonDescent :
  Descent.ConsumerNonDescentWitness
    realifiedChiralObserver
    Dynamics.futureBranch
realifiedFutureBranchNonDescent =
  Descent.consumerNonDescentWitness
    Dynamics.leftSeed
    Dynamics.rightSeed
    leftRightRealifiedCollision
    Dynamics.futureSeedsSeparate

realifiedCannotPayHandedFutureBranch :
  Descent.ConsumerSufficient realifiedChiralObserver Dynamics.futureBranch → ⊥
realifiedCannotPayHandedFutureBranch =
  Descent.nonDescentWitnessBlocksSufficiency realifiedFutureBranchNonDescent

------------------------------------------------------------------------
-- Realified sector is sufficient for the coarser racemic/nonracemic consumer.
------------------------------------------------------------------------

data RacemicStatus : Set where
  racemicClass : RacemicStatus
  nonRacemicClass : RacemicStatus

racemicStatus : Dynamics.ChiralBiasState → RacemicStatus
racemicStatus Dynamics.leftAmplified = nonRacemicClass
racemicStatus Dynamics.leftSeed = nonRacemicClass
racemicStatus Dynamics.racemic = racemicClass
racemicStatus Dynamics.rightSeed = nonRacemicClass
racemicStatus Dynamics.rightAmplified = nonRacemicClass

statusOfRealifiedSector : RealDescent.RealifiedC3Sector → RacemicStatus
statusOfRealifiedSector RealDescent.fixedRealAxis = racemicClass
statusOfRealifiedSector RealDescent.transverseConjugatePlane = nonRacemicClass

racemicStatusFactorsThroughRealifiedSector :
  Descent.FactorsThrough realifiedChiralObserver racemicStatus
racemicStatusFactorsThroughRealifiedSector =
  Factorized.factorizedRefinement
    statusOfRealifiedSector
    factorLaw
  where
    factorLaw :
      (x : Dynamics.ChiralBiasState) →
      racemicStatus x ≡ statusOfRealifiedSector (realifiedChiralObserver x)
    factorLaw Dynamics.leftAmplified = refl
    factorLaw Dynamics.leftSeed = refl
    factorLaw Dynamics.racemic = refl
    factorLaw Dynamics.rightSeed = refl
    factorLaw Dynamics.rightAmplified = refl

realifiedSufficientForRacemicStatus :
  Descent.ConsumerSufficient realifiedChiralObserver racemicStatus
realifiedSufficientForRacemicStatus =
  Descent.fibreConstantIsConsumerSufficient
    (Descent.factorsThroughImpliesFibreConstant
      racemicStatusFactorsThroughRealifiedSector)

------------------------------------------------------------------------
-- Phase strictly refines the realified observer for the handedness consumer;
-- phase plus magnitude then exactly reopens the full finite state.
------------------------------------------------------------------------

realifiedFactorsThroughPhase :
  Descent.FactorsThrough ChiralC3.chiralPhase realifiedChiralObserver
realifiedFactorsThroughPhase =
  Factorized.factorizedRefinement
    Carrier.chemRealifiedSector
    (λ x → refl)

phasePaysHandedFutureBranch :
  Descent.ConsumerSufficient ChiralC3.chiralPhase Dynamics.futureBranch
phasePaysHandedFutureBranch = Recoverable.phaseIsSufficientForFutureBranch

phaseStillDoesNotPayIdentity :
  Descent.ConsumerSufficient ChiralC3.chiralPhase Recoverable.identityConsumer → ⊥
phaseStillDoesNotPayIdentity = Recoverable.phaseCannotPayIdentityConsumer

record ChiralRealDescentObserverBoundary : Set where
  constructor chiralRealDescentObserverBoundary
  field
    fixedVsTransverseObserverPaid : Bool
    realifiedPaysRacemicStatus : Bool
    realifiedPaysHandedBranch : Bool
    phasePaysHandedBranch : Bool
    phasePaysFullIdentity : Bool
    phaseMagnitudeReopensFullIdentity : Bool
    realifiedPlaneIsPhysicalQuantumPlane : Bool

canonicalChiralRealDescentObserverBoundary : ChiralRealDescentObserverBoundary
canonicalChiralRealDescentObserverBoundary =
  chiralRealDescentObserverBoundary
    true true false true false true false
