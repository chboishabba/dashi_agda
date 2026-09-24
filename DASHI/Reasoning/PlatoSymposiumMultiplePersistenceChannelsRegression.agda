module DASHI.Reasoning.PlatoSymposiumMultiplePersistenceChannelsRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Reasoning.PlatoSymposiumMultiplePersistenceChannelsExact as Bridge

persistenceLabelDoesNotDetermineMechanism :
  Bridge.persistenceLabelDeterminesContinuityMechanism
    Bridge.canonicalPlatoMultiplePersistenceBoundary ≡ false
persistenceLabelDoesNotDetermineMechanism = refl

memoryPersistenceIsNotTeachingPersistence :
  Bridge.memoryPersistenceDefinitionallyEqualsTeachingPersistence
    Bridge.canonicalPlatoMultiplePersistenceBoundary ≡ false
memoryPersistenceIsNotTeachingPersistence = refl

teachingPersistenceIsNotInstitutionalRevision :
  Bridge.teachingPersistenceDefinitionallyEqualsAppendOnlyRevision
    Bridge.canonicalPlatoMultiplePersistenceBoundary ≡ false
teachingPersistenceIsNotInstitutionalRevision = refl

platonicPersistenceDoesNotOwnDashiChannels :
  Bridge.diotimaPersistenceOwnsDashiContinuityMechanisms
    Bridge.canonicalPlatoMultiplePersistenceBoundary ≡ false
platonicPersistenceDoesNotOwnDashiChannels = refl

existingOwnersAreReused :
  Bridge.existingPersistenceOwnersReused ≡ true
existingOwnersAreReused = refl
