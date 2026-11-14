{-# OPTIONS --safe #-}
module DASHI.Biology.AvianMagnetoreceptionStreamFiniteCore where

open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- GOLDEN: MECHANISM / EVIDENCE / CLAIM-GRADE SEPARATION
-- No postulates, holes, termination escapes or operational gene designs.
--
-- Copyright/attribution:
-- The Thought Emporium, "Genetic Modification To Sense Magnetic Fields",
-- Whose Gene #11, streamed 17 June 2020, is a science/engineering
-- discussion and speculative proposal, not a published intervention.
-- Original experimental science remains attributed to its paper authors.
--
-- Every theorem below concerns *constructors in a finite vocabulary*.
-- It does not prove or disprove a biological mechanism in an organism.
------------------------------------------------------------------------

data NoWitness : Set where

data Mechanism : Set where
  cryptochromeRadicalPair : Mechanism
  vestibularInduction : Mechanism
  hepaticMacrophage : Mechanism
  biogenicMagnetiteCandidate : Mechanism
  magRCandidate : Mechanism

data AssayKind : Set where
  cellFreePhotochemicalAssay : AssayKind
  neuralActivityMarker : AssayKind
  wholeBrainImaging : AssayKind
  homingBehavior : AssayKind
  humanEEG : AssayKind
  humanConsciousPerception : AssayKind
  humanGeneticGainOfFunction : AssayKind

data SourceClaimTier : Set where
  videoDiscussion : SourceClaimTier
  proposedMechanism : SourceClaimTier
  reportedObservation : SourceClaimTier
  replicatedCausalMechanism : SourceClaimTier
  demonstratedHumanEnhancement : SourceClaimTier

data SpeciesContext : Set where
  pigeon : SpeciesContext
  europeanRobin : SpeciesContext
  human : SpeciesContext

data SensoryCompartment : Set where
  retina : SensoryCompartment
  vestibularInnerEar : SensoryCompartment
  liverMacrophage : SensoryCompartment
  corticalEEG : SensoryCompartment

data FieldChange : Set where
  stationaryLoopConstantFlux : FieldChange
  changingFluxThroughLoop : FieldChange

data FaradayInductionPremise : FieldChange → Set where
  varyingFluxWitness : FaradayInductionPremise changingFluxThroughLoop

constantFluxNotChangingFlux :
  stationaryLoopConstantFlux ≡ changingFluxThroughLoop → NoWitness
constantFluxNotChangingFlux ()

stationaryConstantFluxDoesNotSupplyInductionPremise :
  FaradayInductionPremise stationaryLoopConstantFlux → NoWitness
stationaryConstantFluxDoesNotSupplyInductionPremise ()

data IndependentHumanGainReceipt : SourceClaimTier → Set where
  humanGainIndependentlyDemonstrated :
    IndependentHumanGainReceipt demonstratedHumanEnhancement

videoDoesNotProveHumanGain :
  IndependentHumanGainReceipt videoDiscussion → NoWitness
videoDoesNotProveHumanGain ()

mechanismProposalDoesNotProveHumanGain :
  IndependentHumanGainReceipt proposedMechanism → NoWitness
mechanismProposalDoesNotProveHumanGain ()

observationDoesNotProveHumanGain :
  IndependentHumanGainReceipt reportedObservation → NoWitness
observationDoesNotProveHumanGain ()

data AssayTransport : AssayKind → AssayKind → Set where
  sameCellFreeAssay :
    AssayTransport cellFreePhotochemicalAssay cellFreePhotochemicalAssay
  sameNeuralMarkerAssay :
    AssayTransport neuralActivityMarker neuralActivityMarker
  sameHomingAssay :
    AssayTransport homingBehavior homingBehavior

cryptochromeInVitroNotHomingBehavior :
  AssayTransport cellFreePhotochemicalAssay homingBehavior → NoWitness
cryptochromeInVitroNotHomingBehavior ()

neuralMarkerNotConsciousExperience :
  AssayTransport neuralActivityMarker humanConsciousPerception → NoWitness
neuralMarkerNotConsciousExperience ()

humanEEGNotHumanGeneticEnhancement :
  AssayTransport humanEEG humanGeneticGainOfFunction → NoWitness
humanEEGNotHumanGeneticEnhancement ()

data CrossSpeciesTransport : SpeciesContext → SpeciesContext → Set where
  pigeonReflexive : CrossSpeciesTransport pigeon pigeon
  robinReflexive : CrossSpeciesTransport europeanRobin europeanRobin
  humanReflexive : CrossSpeciesTransport human human

pigeonObservationNotHumanGain :
  CrossSpeciesTransport pigeon human → NoWitness
pigeonObservationNotHumanGain ()

robinInVitroNotHumanGain :
  CrossSpeciesTransport europeanRobin human → NoWitness
robinInVitroNotHumanGain ()

data ExclusiveMechanismProof : Mechanism → Set where

oneMechanismNotExclusive :
  ExclusiveMechanismProof vestibularInduction → NoWitness
oneMechanismNotExclusive ()

------------------------------------------------------------------------
-- Claims of tissue-specific successful editing, delivery and awareness are
-- deliberately NOT admitted by any source-only constructor above.
------------------------------------------------------------------------
