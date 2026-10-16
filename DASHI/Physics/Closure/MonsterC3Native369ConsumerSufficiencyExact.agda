module DASHI.Physics.Closure.MonsterC3Native369ConsumerSufficiencyExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Consumer
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteProjectorModelExact as Model
import DASHI.Physics.Chemistry.AmmoniaMonster3BPhaseQuotientNonFactorabilityExact as PhaseNF
import DASHI.Physics.Chemistry.AmmoniaMonster3BNative369FineCarrierExact as Native369

------------------------------------------------------------------------
-- CONSUMER SUFFICIENCY OF THE EXACT C3 QUOTIENT
--
-- The phase intertwiner is exact, but exactness is consumer-relative.  For a
-- phase/character consumer, the phase observer is sufficient.  For consumers
-- that need the fine zeta microstate, F3^6 weight, or Fin90 multiplicity, the
-- separating pairs already built in PhaseNF prove non-descent.
--
-- The native-369 fine coordinate, by contrast, has a two-sided inverse to the
-- complete zeta model basis and is therefore sufficient for the fine-state
-- consumer.
------------------------------------------------------------------------

State : Set
State = Model.ZetaModelBasis

phaseObserver : State → _
phaseObserver = PhaseNF.modelPhase

phaseConsumer : State → _
phaseConsumer = PhaseNF.modelPhase

weightConsumer : State → H.X6
weightConsumer = Model.weightPosition

multiplicityConsumer : State → _
multiplicityConsumer = Model.multiplicityCoordinate

fineStateConsumer : State → State
fineStateConsumer state = state

native369Observer : State → Native369.Native369ZetaCoordinate
native369Observer = Native369.modelToNative369

phaseObserverSufficientForPhase :
  Consumer.ConsumerSufficient phaseObserver phaseConsumer
phaseObserverSufficientForPhase left right same = same

------------------------------------------------------------------------
-- Non-descent witnesses.
------------------------------------------------------------------------

weightOutcomeDifferent :
  weightConsumer PhaseNF.weightState0 ≡ weightConsumer PhaseNF.weightState1 → ⊥
weightOutcomeDifferent equality =
  PhaseNF.zerNotPos (cong H.x0 equality)

phaseWeightNonDescent :
  Consumer.ConsumerNonDescentWitness phaseObserver weightConsumer
phaseWeightNonDescent =
  Consumer.consumerNonDescentWitness
    PhaseNF.weightState0
    PhaseNF.weightState1
    PhaseNF.samePhaseWeightPair
    weightOutcomeDifferent

phaseObserverNotSufficientForWeight :
  Consumer.ConsumerSufficient phaseObserver weightConsumer → ⊥
phaseObserverNotSufficientForWeight =
  Consumer.nonDescentWitnessBlocksSufficiency phaseWeightNonDescent

multiplicityOutcomeDifferent :
  multiplicityConsumer PhaseNF.multiplicityState0
  ≡ multiplicityConsumer PhaseNF.multiplicityState1 → ⊥
multiplicityOutcomeDifferent = PhaseNF.finZeroNotOne

phaseMultiplicityNonDescent :
  Consumer.ConsumerNonDescentWitness phaseObserver multiplicityConsumer
phaseMultiplicityNonDescent =
  Consumer.consumerNonDescentWitness
    PhaseNF.multiplicityState0
    PhaseNF.multiplicityState1
    PhaseNF.samePhaseMultiplicityPair
    multiplicityOutcomeDifferent

phaseObserverNotSufficientForMultiplicity :
  Consumer.ConsumerSufficient phaseObserver multiplicityConsumer → ⊥
phaseObserverNotSufficientForMultiplicity =
  Consumer.nonDescentWitnessBlocksSufficiency phaseMultiplicityNonDescent

fineStateOutcomeDifferent :
  fineStateConsumer PhaseNF.weightState0
  ≡ fineStateConsumer PhaseNF.weightState1 → ⊥
fineStateOutcomeDifferent = PhaseNF.weightStatesDistinct

phaseFineStateNonDescent :
  Consumer.ConsumerNonDescentWitness phaseObserver fineStateConsumer
phaseFineStateNonDescent =
  Consumer.consumerNonDescentWitness
    PhaseNF.weightState0
    PhaseNF.weightState1
    PhaseNF.samePhaseWeightPair
    fineStateOutcomeDifferent

phaseObserverNotSufficientForFineState :
  Consumer.ConsumerSufficient phaseObserver fineStateConsumer → ⊥
phaseObserverNotSufficientForFineState =
  Consumer.nonDescentWitnessBlocksSufficiency phaseFineStateNonDescent

phaseFineStateDoesNotFactor :
  Consumer.FactorsThrough phaseObserver fineStateConsumer → ⊥
phaseFineStateDoesNotFactor =
  Consumer.nonDescentWitnessBlocksFactorization phaseFineStateNonDescent

------------------------------------------------------------------------
-- Native369 coordinate is sufficient for the fine-state consumer.
------------------------------------------------------------------------

native369ObserverSufficientForFineState :
  Consumer.ConsumerSufficient native369Observer fineStateConsumer
native369ObserverSufficientForFineState left right sameNative =
  trans
    (sym (Native369.model369RoundTrip left))
    (trans
      (cong Native369.native369ToModel sameNative)
      (Native369.model369RoundTrip right))

record ConsumerSufficiencyBoundary : Set where
  constructor consumerSufficiencyBoundary
  field
    phaseSufficientForPhaseConsumers : Bool
    phaseSufficientForPhaseConsumersIsTrue : phaseSufficientForPhaseConsumers ≡ true
    phaseSufficientForWeightConsumers : Bool
    phaseSufficientForWeightConsumersIsFalse : phaseSufficientForWeightConsumers ≡ false
    phaseSufficientForMultiplicityConsumers : Bool
    phaseSufficientForMultiplicityConsumersIsFalse : phaseSufficientForMultiplicityConsumers ≡ false
    phaseSufficientForFineStateConsumers : Bool
    phaseSufficientForFineStateConsumersIsFalse : phaseSufficientForFineStateConsumers ≡ false
    native369FineCoordinateSufficientForFineState : Bool
    native369FineCoordinateSufficientForFineStateIsTrue :
      native369FineCoordinateSufficientForFineState ≡ true
    phaseQuotientSufficientForMicrostateEntropyConsumer : Bool
    phaseQuotientSufficientForMicrostateEntropyConsumerIsFalse :
      phaseQuotientSufficientForMicrostateEntropyConsumer ≡ false
    interpretation : String

open ConsumerSufficiencyBoundary public

canonicalConsumerSufficiencyBoundary : ConsumerSufficiencyBoundary
canonicalConsumerSufficiencyBoundary =
  consumerSufficiencyBoundary
    true refl
    false refl
    false refl
    false refl
    true refl
    false refl
    "The exact NH3/Monster C3 quotient is sufficient for phase/character consumers and formally insufficient for Monster microstate, weight, multiplicity and microstate-entropy consumers. The native-369 fine coordinate is sufficient for the complete finite model state."
