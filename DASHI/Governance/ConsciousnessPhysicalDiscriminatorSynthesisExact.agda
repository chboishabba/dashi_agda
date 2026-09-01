module DASHI.Governance.ConsciousnessPhysicalDiscriminatorSynthesisExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.DiscriminatorSynthesisExact as Disc
import DASHI.Governance.ConsciousnessRealisedTopologyCrossPollinationExact as Topology
import DASHI.Governance.Lerchner2026AbstractionFallacySourceBridgeExact as Lerchner
import DASHI.Biology.Levin.SubstrateConstrainedComputation as LevinSubstrate
import DASHI.Biology.Levin.ObserverRelativePolycomputation as LevinObserver

------------------------------------------------------------------------
-- CONSCIOUSNESS PHYSICAL-DISCRIMINATOR SYNTHESIS
--
-- Substrate-sensitive consciousness theories do not close by merely asserting
-- that physics matters.  They owe a coordinate-level discriminator capable of
-- separating live hypotheses that collide under the existing behavioural /
-- computational observer.
------------------------------------------------------------------------

data TheoryWorld : Set where
  topologySufficient substrateSensitive : TheoryWorld

-- Both theories can agree on the same behaviour / nominal computational
-- surface while disagreeing over whether an additional physical coordinate is
-- constitutively relevant.
data ExistingSurface : Set where sameBehaviourAndComputation : ExistingSurface

existingSurface : TheoryWorld → ExistingSurface
existingSurface _ = sameBehaviourAndComputation

canonicalTheoryCollision : Disc.CurrentObserverCollision existingSurface
canonicalTheoryCollision = Disc.currentObserverCollision topologySufficient substrateSensitive refl

------------------------------------------------------------------------
-- Candidate physical coordinate.  This is intentionally schematic: a real
-- application must replace the finite tags with measured physical coordinates,
-- calibration, intervention semantics and source/measurement provenance.
------------------------------------------------------------------------

data PhysicalCoordinateObservation : Set where
  topologyOnlyResponse substrateSensitiveResponse : PhysicalCoordinateObservation

physicalCoordinateObservation : TheoryWorld → PhysicalCoordinateObservation
physicalCoordinateObservation topologySufficient = topologyOnlyResponse
physicalCoordinateObservation substrateSensitive = substrateSensitiveResponse

physicalCoordinateBundle : Disc.ExperimentBundle TheoryWorld
physicalCoordinateBundle =
  Disc.experimentBundle
    PhysicalCoordinateObservation
    physicalCoordinateObservation
    1
    "candidate physical-coordinate discriminator for competing consciousness theories"
    "application must supply measurement calibration, physical intervention semantics and provenance"

physicalCoordinateSeparates :
  Disc.BundleSeparates physicalCoordinateBundle topologySufficient substrateSensitive
physicalCoordinateSeparates = Disc.bundleSeparates (λ ())

physicalLanguageExtension : Disc.DiscriminatingLanguageExtension existingSurface
physicalLanguageExtension =
  Disc.discriminatingLanguageExtension
    canonicalTheoryCollision
    physicalCoordinateBundle
    physicalCoordinateSeparates

joinedLanguageReallySeparates :
  Disc.joinedObservation existingSurface physicalCoordinateBundle topologySufficient
  ≡ Disc.joinedObservation existingSurface physicalCoordinateBundle substrateSensitive → ⊥
joinedLanguageReallySeparates = Disc.extensionJoinSeparates physicalLanguageExtension

------------------------------------------------------------------------
-- Explicit empirical burden.
------------------------------------------------------------------------

record PhysicalTheoryDiscriminatorReceipt : Set where
  constructor physical-theory-discriminator-receipt
  field
    physicalCoordinateReference : String
    realisedTopologyReference : String
    interventionReference : String
    measurementReference : String
    calibrationReference : String
    nuisanceReference : String
    competingTheoryPredictionReference : String
    provenanceReference : String
    validationReference : String

------------------------------------------------------------------------
-- Boundary: neither Lerchner-style substrate sensitivity nor Levin-style
-- observer-relative / substrate-constrained computation is promoted directly
-- to phenomenal truth.  Both instead motivate a better discriminator language.
------------------------------------------------------------------------

record ConsciousnessPhysicalDiscriminatorBoundary : Set where
  constructor consciousness-physical-discriminator-boundary
  field
    physicalConstitutionMattersStatementClosesTheoryCollision : Bool
    physicalConstitutionMattersStatementClosesTheoryCollisionIsFalse :
      physicalConstitutionMattersStatementClosesTheoryCollision ≡ false
    behaviouralAgreementSettlesPhysicalInstantiationTheory : Bool
    behaviouralAgreementSettlesPhysicalInstantiationTheoryIsFalse :
      behaviouralAgreementSettlesPhysicalInstantiationTheory ≡ false
    nominalComputationSettlesRealisedTopology : Bool
    nominalComputationSettlesRealisedTopologyIsFalse :
      nominalComputationSettlesRealisedTopology ≡ false
    observerRelativeReadingMakesPhysicalTheoryArbitrary : Bool
    observerRelativeReadingMakesPhysicalTheoryArbitraryIsFalse :
      observerRelativeReadingMakesPhysicalTheoryArbitrary ≡ false
    coordinateLevelDiscriminatorRequired : Bool
    coordinateLevelDiscriminatorRequiredIsTrue :
      coordinateLevelDiscriminatorRequired ≡ true
    discriminatorResultAutomaticallyProvesConsciousness : Bool
    discriminatorResultAutomaticallyProvesConsciousnessIsFalse :
      discriminatorResultAutomaticallyProvesConsciousness ≡ false
    moralPolicyStillRequiresIndependentGovernance : Bool
    moralPolicyStillRequiresIndependentGovernanceIsTrue :
      moralPolicyStillRequiresIndependentGovernance ≡ true
    reading : String

canonicalConsciousnessPhysicalDiscriminatorBoundary :
  ConsciousnessPhysicalDiscriminatorBoundary
canonicalConsciousnessPhysicalDiscriminatorBoundary =
  consciousness-physical-discriminator-boundary
    false refl
    false refl
    false refl
    false refl
    true refl
    false refl
    true refl
    "Competing consciousness theories that collide under behaviour and computational description require coordinate-level physical discriminators. Lerchner-style substrate sensitivity and Levin-style substrate/observer constraints motivate the discriminator burden but do not themselves prove phenomenal instantiation; realised topology, measurement calibration, nuisance control, provenance and independent moral governance remain separate."

------------------------------------------------------------------------
-- Imported canonical boundaries remain visible to downstream consumers.
------------------------------------------------------------------------

realisedTopologyBoundary : Topology.ConsciousnessRealisedTopologyBoundary
realisedTopologyBoundary = Topology.canonicalConsciousnessRealisedTopologyBoundary

lerchnerSourceBoundary : Lerchner.LerchnerSourceAuthorityBoundary
lerchnerSourceBoundary = Lerchner.canonicalLerchnerSourceAuthorityBoundary

levinSubstrateBoundary : LevinSubstrate.SubstrateConstrainedComputationBoundary
levinSubstrateBoundary = LevinSubstrate.canonicalSubstrateConstrainedComputationBoundary

levinObserverBoundary : LevinObserver.ObserverRelativePolycomputationBoundary
levinObserverBoundary = LevinObserver.canonicalObserverRelativePolycomputationBoundary
