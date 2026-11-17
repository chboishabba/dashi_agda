module DASHI.Biology.IITIIT4ConsumerDescentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Biology.IIT369MatchedAlgebraControlExact as Algebra
import DASHI.Biology.IITPointedTernary27TriadicNonDescentExact as Triadic
import DASHI.Reasoning.IITBrainMaleCNSConsumerBoundaryExact as Brain

------------------------------------------------------------------------
-- IIT OBSERVABLES ARE CONSUMER-RELATIVE OBSERVERS
------------------------------------------------------------------------

data AlgebraVariant : Set where
  z9CyclicVariant : AlgebraVariant
  f3SquaredVariant : AlgebraVariant

nineStateCardinalityObservation : AlgebraVariant → Nat
nineStateCardinalityObservation z9CyclicVariant = 9
nineStateCardinalityObservation f3SquaredVariant = 9

isProductGroupConsumer : AlgebraVariant → Bool
isProductGroupConsumer z9CyclicVariant = false
isProductGroupConsumer f3SquaredVariant = true

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

cardinalityLosesGroupLaw :
  Descent.ConsumerNonDescentWitness
    nineStateCardinalityObservation
    isProductGroupConsumer
cardinalityLosesGroupLaw =
  Descent.consumerNonDescentWitness
    z9CyclicVariant
    f3SquaredVariant
    refl
    falseNotTrue

cardinalityCannotFactorGroupLaw :
  Descent.FactorsThrough
    nineStateCardinalityObservation
    isProductGroupConsumer → ⊥
cardinalityCannotFactorGroupLaw =
  Descent.nonDescentWitnessBlocksFactorization cardinalityLosesGroupLaw

selectedCubieObservationCannotRecoverTriadicFace :
  Descent.FactorsThrough
    Triadic.selectedCubiesObserver
    Triadic.triadicFaceConsumer → ⊥
selectedCubieObservationCannotRecoverTriadicFace =
  Triadic.selectedCubiesDoNotDetermineTriadicFace

data IITObservationLevel : Set where
  systemPhiOnly : IITObservationLevel
  distinctionsOnly : IITObservationLevel
  fullCauseEffectStructure : IITObservationLevel

record ConsumerFactorizationObligation : Set where
  constructor consumerFactorizationObligation
  field
    observationLevel : IITObservationLevel
    consumerLabel : String
    factorizationReceipt : String
    factorizationPaid : Bool

open ConsumerFactorizationObligation public

record IITConsumerDescentBoundary : Set where
  constructor iitConsumerDescentBoundary
  field
    cardinalityNonDescentKernelProved : Bool
    selectedCubieTriadicFaceNonDescentKernelProved : Bool
    matchedZ9F3SquaredPhiProfileCollisionNumericallyObserved : Bool
    numericPhiCollisionIsKernelProof : Bool
    consumerFactorizationRequiredPerClaim : Bool
    scalarPhiAutomaticallyRecoversMemoryPolicyOrPhenomenalIdentity : Bool
    fullStructureAutomaticallyWorldComplete : Bool

open IITConsumerDescentBoundary public

canonicalIITConsumerDescentBoundary : IITConsumerDescentBoundary
canonicalIITConsumerDescentBoundary =
  iitConsumerDescentBoundary true true true false true false false

numericCollisionDoesNotSelfPromote :
  numericPhiCollisionIsKernelProof canonicalIITConsumerDescentBoundary ≡ false
numericCollisionDoesNotSelfPromote = refl

consumerPaymentCannotBeSkipped :
  consumerFactorizationRequiredPerClaim canonicalIITConsumerDescentBoundary ≡ true
consumerPaymentCannotBeSkipped = refl

algebraControlBoundary : Algebra.IIT369AlgebraControlBoundary
algebraControlBoundary = Algebra.canonicalIIT369AlgebraControlBoundary

brainConsumerBoundary : Brain.BrainMaleCNSIITBoundary
brainConsumerBoundary = Brain.canonicalBrainMaleCNSIITBoundary
