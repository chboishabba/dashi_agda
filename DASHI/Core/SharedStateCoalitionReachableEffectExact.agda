module DASHI.Core.SharedStateCoalitionReachableEffectExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

data Actor : Set where actorA actorB : Actor
data SharedCoordinate : Set where directoryName lightLevel robotPose temperature : SharedCoordinate

data CanWrite : Actor → SharedCoordinate → Set where
  aWritesDirectory : CanWrite actorA directoryName
  aWritesLight : CanWrite actorA lightLevel
  aWritesPose : CanWrite actorA robotPose
  aWritesTemperature : CanWrite actorA temperature

data CanObserve : Actor → SharedCoordinate → Set where
  bReadsDirectory : CanObserve actorB directoryName
  bSeesLight : CanObserve actorB lightLevel
  bSeesPose : CanObserve actorB robotPose
  bReadsTemperature : CanObserve actorB temperature

record PotentialChannel (sender receiver : Actor) (coordinate : SharedCoordinate) : Set where
  constructor potential-channel
  field
    writer : CanWrite sender coordinate
    observer : CanObserve receiver coordinate

filesystemDirectoryIsPotentialChannel : PotentialChannel actorA actorB directoryName
filesystemDirectoryIsPotentialChannel = potential-channel aWritesDirectory bReadsDirectory
physicalLightIsPotentialChannel : PotentialChannel actorA actorB lightLevel
physicalLightIsPotentialChannel = potential-channel aWritesLight bSeesLight
robotPoseIsPotentialChannel : PotentialChannel actorA actorB robotPose
robotPoseIsPotentialChannel = potential-channel aWritesPose bSeesPose
temperatureIsPotentialChannel : PotentialChannel actorA actorB temperature
temperatureIsPotentialChannel = potential-channel aWritesTemperature bReadsTemperature

data DeclaredCommunicationChannel : SharedCoordinate → Set where
notDeclaredDoesNotRemoveDirectoryChannel : DeclaredCommunicationChannel directoryName → ⊥
notDeclaredDoesNotRemoveDirectoryChannel ()

data Effect : Set where discoverWeakness useCredential : Effect
data IndividualCanCause : Actor → Effect → Set where
  aCanDiscover : IndividualCanCause actorA discoverWeakness
  bCanUseCredential : IndividualCanCause actorB useCredential

data CoalitionEffect : Set where combinedExternalReach : CoalitionEffect

record CoalitionReachableEffect : Set where
  constructor coalition-reachable-effect
  field
    firstContribution : IndividualCanCause actorA discoverWeakness
    secondContribution : IndividualCanCause actorB useCredential
    communication : PotentialChannel actorA actorB directoryName
    emergentEffect : CoalitionEffect

canonicalCoalitionReachableEffect : CoalitionReachableEffect
canonicalCoalitionReachableEffect =
  coalition-reachable-effect aCanDiscover bCanUseCredential
    filesystemDirectoryIsPotentialChannel combinedExternalReach

data CapabilityKind : Set where delegationCapability replicationCapability : CapabilityKind
delegationKindIsNotReplicationKind : delegationCapability ≡ replicationCapability → ⊥
delegationKindIsNotReplicationKind ()

data AssuranceLevel : Set where deviceLocalSafety wholeSystemClosure : AssuranceLevel
localSafetyIsNotSystemClosure : deviceLocalSafety ≡ wholeSystemClosure → ⊥
localSafetyIsNotSystemClosure ()

record SharedStateCoalitionBoundary : Set where
  constructor shared-state-coalition-boundary
  field
    undeclaredChannelMeansNoChannel : Bool
    undeclaredChannelMeansNoChannelIsFalse : undeclaredChannelMeansNoChannel ≡ false
    physicalEnvironmentCannotCarryMessages : Bool
    physicalEnvironmentCannotCarryMessagesIsFalse : physicalEnvironmentCannotCarryMessages ≡ false
    individualBoundsImplyCollectiveBounds : Bool
    individualBoundsImplyCollectiveBoundsIsFalse : individualBoundsImplyCollectiveBounds ≡ false
    delegationImpliesReplicationPermission : Bool
    delegationImpliesReplicationPermissionIsFalse : delegationImpliesReplicationPermission ≡ false
    localDeviceSafetyImpliesSystemSafety : Bool
    localDeviceSafetyImpliesSystemSafetyIsFalse : localDeviceSafetyImpliesSystemSafety ≡ false
    sandboxLabelProvesReachableEffectClosure : Bool
    sandboxLabelProvesReachableEffectClosureIsFalse : sandboxLabelProvesReachableEffectClosure ≡ false
    reading : String

canonicalSharedStateCoalitionBoundary : SharedStateCoalitionBoundary
canonicalSharedStateCoalitionBoundary =
  shared-state-coalition-boundary
    false refl false refl false refl false refl false refl false refl
    "Write(A,X) plus observe(B,X) yields a potential channel independently of declared purpose; physical state can be shared memory; individually bounded actors need not bound a coalition; delegation is not replication; local device safety and sandbox labels do not establish reachable-effect closure."
