module DASHI.Physics.Closure.MonsterC3Native369ConsumerSufficiencyExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Consumer
import DASHI.Moonshine.Monster3BCentralCharacterInertiaExact as Monster3B
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteProjectorModelExact as Model
import DASHI.Moonshine.Monster3BWZetaBasisVectorRecognitionCorrectionExact as BasisCorrection
import DASHI.Physics.Chemistry.AmmoniaMonster3BPhaseQuotientNonFactorabilityExact as PhaseNF
import DASHI.Physics.Chemistry.AmmoniaMonster3BNative369FineCarrierExact as Native369

------------------------------------------------------------------------
-- This entire owner is about the finite MODEL BASIS-LABEL carrier.
-- It makes no claim that a finite label is an arbitrary vector in W_zeta.
------------------------------------------------------------------------

BasisLabelState : Set
BasisLabelState = Model.ZetaModelBasis

phaseObserver : BasisLabelState → Monster3B.CentralPhase3
phaseObserver = PhaseNF.modelPhase

phaseConsumer : BasisLabelState → Monster3B.CentralPhase3
phaseConsumer = PhaseNF.modelPhase

weightConsumer : BasisLabelState → H.X6
weightConsumer = Model.weightPosition

multiplicityConsumer : BasisLabelState → Fin 90
multiplicityConsumer = Model.multiplicityCoordinate

basisLabelConsumer : BasisLabelState → BasisLabelState
basisLabelConsumer state = state

native369Observer : BasisLabelState → Native369.Native369ZetaCoordinate
native369Observer = Native369.modelToNative369

phaseObserverSufficientForPhase :
  Consumer.ConsumerSufficient phaseObserver phaseConsumer
phaseObserverSufficientForPhase left right same = same

weightOutcomeDifferent :
  weightConsumer PhaseNF.weightState0 ≡ weightConsumer PhaseNF.weightState1 → ⊥
weightOutcomeDifferent equality =
  PhaseNF.zerNotPos (cong H.x0 equality)

phaseWeightNonDescent :
  Consumer.ConsumerNonDescentWitness phaseObserver weightConsumer
phaseWeightNonDescent =
  Consumer.consumerNonDescentWitness
    PhaseNF.weightState0 PhaseNF.weightState1
    PhaseNF.samePhaseWeightPair weightOutcomeDifferent

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
    PhaseNF.multiplicityState0 PhaseNF.multiplicityState1
    PhaseNF.samePhaseMultiplicityPair multiplicityOutcomeDifferent

phaseObserverNotSufficientForMultiplicity :
  Consumer.ConsumerSufficient phaseObserver multiplicityConsumer → ⊥
phaseObserverNotSufficientForMultiplicity =
  Consumer.nonDescentWitnessBlocksSufficiency phaseMultiplicityNonDescent

basisLabelOutcomeDifferent :
  basisLabelConsumer PhaseNF.weightState0
  ≡ basisLabelConsumer PhaseNF.weightState1 → ⊥
basisLabelOutcomeDifferent = PhaseNF.weightStatesDistinct

phaseBasisLabelNonDescent :
  Consumer.ConsumerNonDescentWitness phaseObserver basisLabelConsumer
phaseBasisLabelNonDescent =
  Consumer.consumerNonDescentWitness
    PhaseNF.weightState0 PhaseNF.weightState1
    PhaseNF.samePhaseWeightPair basisLabelOutcomeDifferent

phaseObserverNotSufficientForBasisLabel :
  Consumer.ConsumerSufficient phaseObserver basisLabelConsumer → ⊥
phaseObserverNotSufficientForBasisLabel =
  Consumer.nonDescentWitnessBlocksSufficiency phaseBasisLabelNonDescent

phaseBasisLabelDoesNotFactor :
  Consumer.FactorsThrough phaseObserver basisLabelConsumer → ⊥
phaseBasisLabelDoesNotFactor =
  Consumer.nonDescentWitnessBlocksFactorization phaseBasisLabelNonDescent

native369ObserverSufficientForBasisLabel :
  Consumer.ConsumerSufficient native369Observer basisLabelConsumer
native369ObserverSufficientForBasisLabel left right sameNative =
  trans
    (sym (Native369.model369RoundTrip left))
    (trans
      (cong Native369.native369ToModel sameNative)
      (Native369.model369RoundTrip right))

------------------------------------------------------------------------
-- Backwards-compatible names.  Their types now make the corrected scope
-- explicit: historical "fine state" means the finite model basis label here.
------------------------------------------------------------------------

fineStateConsumer : BasisLabelState → BasisLabelState
fineStateConsumer = basisLabelConsumer

phaseFineStateNonDescent :
  Consumer.ConsumerNonDescentWitness phaseObserver fineStateConsumer
phaseFineStateNonDescent = phaseBasisLabelNonDescent

phaseObserverNotSufficientForFineState :
  Consumer.ConsumerSufficient phaseObserver fineStateConsumer → ⊥
phaseObserverNotSufficientForFineState = phaseObserverNotSufficientForBasisLabel

phaseFineStateDoesNotFactor :
  Consumer.FactorsThrough phaseObserver fineStateConsumer → ⊥
phaseFineStateDoesNotFactor = phaseBasisLabelDoesNotFactor

native369ObserverSufficientForFineState :
  Consumer.ConsumerSufficient native369Observer fineStateConsumer
native369ObserverSufficientForFineState = native369ObserverSufficientForBasisLabel

record ConsumerSufficiencyBoundary : Set where
  constructor consumerSufficiencyBoundary
  field
    phaseSufficientForPhaseConsumers : Bool
    phaseSufficientForPhaseConsumersIsTrue : phaseSufficientForPhaseConsumers ≡ true
    phaseSufficientForWeightConsumers : Bool
    phaseSufficientForWeightConsumersIsFalse : phaseSufficientForWeightConsumers ≡ false
    phaseSufficientForMultiplicityConsumers : Bool
    phaseSufficientForMultiplicityConsumersIsFalse : phaseSufficientForMultiplicityConsumers ≡ false

    -- Historical projection names retained for downstream consumers.
    phaseSufficientForFineStateConsumers : Bool
    phaseSufficientForFineStateConsumersIsFalse :
      phaseSufficientForFineStateConsumers ≡ false
    native369FineCoordinateSufficientForFineState : Bool
    native369FineCoordinateSufficientForFineStateIsTrue :
      native369FineCoordinateSufficientForFineState ≡ true

    -- Corrected representation-native names.
    phaseSufficientForFiniteBasisLabelConsumers : Bool
    phaseSufficientForFiniteBasisLabelConsumersIsFalse :
      phaseSufficientForFiniteBasisLabelConsumers ≡ false
    native369FineCoordinateSufficientForFiniteBasisLabel : Bool
    native369FineCoordinateSufficientForFiniteBasisLabelIsTrue :
      native369FineCoordinateSufficientForFiniteBasisLabel ≡ true
    finiteBasisLabelConsumerIsWholeLinearVOAStateConsumer : Bool
    finiteBasisLabelConsumerIsWholeLinearVOAStateConsumerIsFalse :
      finiteBasisLabelConsumerIsWholeLinearVOAStateConsumer ≡ false
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
    true refl
    false refl
    false refl
    "The exact NH3/Monster C3 quotient is sufficient for phase/character consumers and formally insufficient for weight, multiplicity and finite Monster basis-label identity. The historical `fine state` names are retained only for that finite-model basis-label consumer. The native-369 coordinate is sufficient for the complete finite model basis label, not for every vector in the literal W_zeta eigenspace; representation-native W_zeta recognition is separately governed by ActualZetaBasisRecognition and H_zeta/S_zeta linear same-object receipts."
