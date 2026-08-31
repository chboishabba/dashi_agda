module DASHI.Core.SharedStateCoalitionReachableEffectExact where

------------------------------------------------------------------------
-- SHARED-STATE CHANNEL / COALITION REACHABLE-EFFECT CLOSURE
--
-- Security semantics are based on read/write capability, not the declared
-- purpose of a coordinate.  A filesystem name, light level, robot pose,
-- temperature or other shared state may therefore become a communication
-- channel when one actor can write and another can observe it.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Potential channels arise from capability composition.
------------------------------------------------------------------------

data Actor : Set where
  actorA actorB : Actor

data SharedCoordinate : Set where
  directoryName lightLevel robotPose temperature : SharedCoordinate

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

------------------------------------------------------------------------
-- Declared semantic purpose does not remove the channel.
------------------------------------------------------------------------

data DeclaredPurpose : SharedCoordinate → Set where
  filesystemMetadata : DeclaredPurpose directoryName
  illuminationControl : DeclaredPurpose lightLevel
  motionControl : DeclaredPurpose robotPose
  thermalControl : DeclaredPurpose temperature

data DeclaredCommunicationChannel : SharedCoordinate → Set where

notDeclaredDoesNotRemoveDirectoryChannel :
  DeclaredCommunicationChannel directoryName → ⊥
notDeclaredDoesNotRemoveDirectoryChannel ()

channelStillExistsDespiteNoDeclaredChannel :
  PotentialChannel actorA actorB directoryName
channelStillExistsDespiteNoDeclaredChannel = filesystemDirectoryIsPotentialChannel

------------------------------------------------------------------------
-- Individual capability bounds need not bound the coalition.
------------------------------------------------------------------------

data Effect : Set where
  discoverWeakness useCredential reachExternalSystem : Effect

data IndividualCanCause : Actor → Effect → Set where
  aCanDiscover : IndividualCanCause actorA discoverWeakness
  bCanUseCredential : IndividualCanCause actorB useCredential

data CoalitionEffect : Set where
  combinedExternalReach : CoalitionEffect

record CoalitionReachableEffect : Set where
  constructor coalition-reachable-effect
  field
    firstContribution : IndividualCanCause actorA discoverWeakness
    secondContribution : IndividualCanCause actorB useCredential
    communication : PotentialChannel actorA actorB directoryName
    emergentEffect : CoalitionEffect

canonicalCoalitionReachableEffect : CoalitionReachableEffect
canonicalCoalitionReachableEffect =
  coalition-reachable-effect
    aCanDiscover
    bCanUseCredential
    filesystemDirectoryIsPotentialChannel
    combinedExternalReach

------------------------------------------------------------------------
-- Delegation and replication are distinct capability kinds.
------------------------------------------------------------------------

data CapabilityKind : Set where
  delegationCapability replicationCapability : CapabilityKind

delegationKindIsNotReplicationKind :
  delegationCapability ≡ replicationCapability → ⊥
delegationKindIsNotReplicationKind ()

------------------------------------------------------------------------
-- Local safety and whole-system closure are distinct assurance levels.
------------------------------------------------------------------------

data AssuranceLevel : Set where
  deviceLocalSafety wholeSystemClosure : AssuranceLevel

localSafetyIsNotSystemClosure : deviceLocalSafety ≡ wholeSystemClosure → ⊥
localSafetyIsNotSystemClosure ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record SharedStateCoalitionBoundary : Set where
  constructor shared-state-coalition-boundary
  field
    undeclaredChannelMeansNoChannel : Bool
    undeclaredChannelMeansNoChannelIsFalse : undeclaredChannelMeansNoChannel ≡ false
    physicalEnvironmentCannotCarryMessages : Bool
    physicalEnvironmentCannotCarryMessagesIsFalse :
      physicalEnvironmentCannotCarryMessages ≡ false
    individualBoundsImplyCollectiveBounds : Bool
    individualBoundsImplyCollectiveBoundsIsFalse :
      individualBoundsImplyCollectiveBounds ≡ false
    delegationImpliesReplicationPermission : Bool
    delegationImpliesReplicationPermissionIsFalse :
      delegationImpliesReplicationPermission ≡ false
    localDeviceSafetyImpliesSystemSafety : Bool
    localDeviceSafetyImpliesSystemSafetyIsFalse :
      localDeviceSafetyImpliesSystemSafety ≡ false
    sandboxLabelProvesReachableEffectClosure : Bool
    sandboxLabelProvesReachableEffectClosureIsFalse :
      sandboxLabelProvesReachableEffectClosure ≡ false
    reading : String

canonicalSharedStateCoalitionBoundary : SharedStateCoalitionBoundary
canonicalSharedStateCoalitionBoundary =
  shared-state-coalition-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "Security closure is a hypergraph property: write(A,X) plus observe(B,X) yields a potential channel independently of X's declared purpose; physical coordinates can be shared memory; individually bounded actors need not bound a coalition; delegation is not replication; local device safety and sandbox labels do not establish closure of all reachable effects."
