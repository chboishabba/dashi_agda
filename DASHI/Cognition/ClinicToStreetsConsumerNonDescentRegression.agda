module DASHI.Cognition.ClinicToStreetsConsumerNonDescentRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Cognition.ClinicToStreetsConsumerNonDescentExact as X

canonicalWitness :
  Descent.ConsumerNonDescentWitness X.atomisingObserver X.structuralConsumer
canonicalWitness = X.canonicalAtomisingNonDescent

atomisingObserverIsNotStructurallySufficient :
  Descent.ConsumerSufficient X.atomisingObserver X.structuralConsumer → ⊥
atomisingObserverIsNotStructurallySufficient =
  X.atomisingObserverBlocksStructuralSufficiency

atomisingObserverCannotFactorStructuralConsumer :
  Descent.FactorsThrough X.atomisingObserver X.structuralConsumer → ⊥
atomisingObserverCannotFactorStructuralConsumer =
  X.atomisingObserverBlocksStructuralFactorisation

contextObserverPaysStructuralConsumer :
  Descent.ConsumerSufficient X.contextObserver X.structuralConsumer
contextObserverPaysStructuralConsumer = X.contextObserverIsStructurallySufficient
