module DASHI.Physics.Chemistry.AmmoniaHydrogenAbstraction369HyperfibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List)
import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as Atomic369
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ChemistryHyperfibreBridgeExact as Fibre
import DASHI.Physics.Chemistry.AmmoniaHydrogenAbstractionMechanismExact as Mechanism

------------------------------------------------------------------------
-- CONCRETE 369 HYPERFIBRE FOR 14NH3 + 1H -> 14NH2 + 1H2
--
-- This fixture carries source/target atomic inventories using the 369 AtomicIndex
-- type.  It does NOT attach persistent individual atom IDs across the reaction;
-- therefore inventory conservation is paid while atom-identity transport is not.
------------------------------------------------------------------------

data ReactionTime : Set where
  beforeCollision afterReaction : ReactionTime

expectedAtoms : ReactionTime → List Atomic369.AtomicIndex
expectedAtoms beforeCollision = Mechanism.reactantAtomicInventory369
expectedAtoms afterReaction = Mechanism.productAtomicInventory369

expectedMolecule : ReactionTime → String
expectedMolecule beforeCollision = "14NH3 + 1H separated reactants"
expectedMolecule afterReaction = "14NH2 + 1H2 separated products"

expectedReactionStage : ReactionTime → Mechanism.AbstractionStage
expectedReactionStage beforeCollision = Mechanism.separatedReactants
expectedReactionStage afterReaction = Mechanism.separatedProducts

atomicSourceRef : ReactionTime → String
atomicSourceRef beforeCollision = "AtomicPeriodicTable369GenerativeExact source 14N + four 1H AtomicIndex inventory"
atomicSourceRef afterReaction = "AtomicPeriodicTable369GenerativeExact target 14N + four 1H AtomicIndex inventory"

molecularSourceRef : ReactionTime → String
molecularSourceRef beforeCollision = "source-backed NH3 + H molecular identity"
molecularSourceRef afterReaction = "source-backed NH2 + H2 molecular identity"

reactionSourceRef : ReactionTime → String
reactionSourceRef beforeCollision = "Espinosa-Garcia/Corchado 2010 PES source-side abstraction state"
reactionSourceRef afterReaction = "Corchado/Espinosa-Garcia/Yang 2011 product-side quantum-dynamics reaction state"

ammoniaAbstraction369System : Fibre.ChemistryHyperfibreSystem
ammoniaAbstraction369System =
  Fibre.chemistryHyperfibreSystem
    ReactionTime
    (λ _ → List Atomic369.AtomicIndex)
    (λ _ → String)
    (λ _ → Mechanism.AbstractionStage)
    (λ _ → ⊤)
    (λ t atoms _ → atoms ≡ expectedAtoms t)
    (λ t molecule stage →
      (molecule ≡ expectedMolecule t) × (stage ≡ expectedReactionStage t))
    (λ t stage _ → stage ≡ expectedReactionStage t)
    atomicSourceRef
    molecularSourceRef
    reactionSourceRef
    (λ _ → "no industrial promotion in this microscopic fixture")
    (λ _ → "NH3-H-abstraction-369-hyperfibre-v1")

sourceFibre : Fibre.ChemistryFibre ammoniaAbstraction369System beforeCollision
sourceFibre =
  Fibre.chemistryFibre
    Mechanism.reactantAtomicInventory369
    "14NH3 + 1H separated reactants"
    Mechanism.separatedReactants
    tt
    refl
    (refl , refl)
    refl
    "14N + four 1H AtomicIndex inventory"
    "NH3 + H source molecular state"
    "source state for PES-2009 abstraction path"
    "not industrial"

targetFibre : Fibre.ChemistryFibre ammoniaAbstraction369System afterReaction
targetFibre =
  Fibre.chemistryFibre
    Mechanism.productAtomicInventory369
    "14NH2 + 1H2 separated products"
    Mechanism.separatedProducts
    tt
    refl
    (refl , refl)
    refl
    "same isotope/species inventory: 14N + four 1H AtomicIndex entries"
    "NH2 + H2 target molecular state"
    "target state for PES-2009 abstraction path"
    "not industrial"

abstractionTransport : Fibre.ChemistryFibreTransport sourceFibre targetFibre
abstractionTransport =
  Fibre.chemistryFibreTransport
    "separatedReactants -> entranceApproach -> saddleRegion -> exitSeparation -> separatedProducts"
    "source and target have matching 14N + four 1H AtomicIndex inventories; no persistent per-atom identity map is asserted"
    "NH3 + H -> NH2 + H2 molecular identity transport"
    "Espinosa-Garcia/Corchado PES-2009 reaction path plus 2011 quantum-dynamics consumer"
    "no industrial/process promotion"
    true refl
    true refl

record HyperformBoundary : Set where
  constructor hyperformBoundary
  field
    literalChemistryHyperfibreInhabited : Bool
    literalChemistryHyperfibreInhabitedIsTrue :
      literalChemistryHyperfibreInhabited ≡ true
    sourceBackedMechanismAttached : Bool
    sourceBackedMechanismAttachedIsTrue : sourceBackedMechanismAttached ≡ true
    atomic369InventoryEndpointsPaid : Bool
    atomic369InventoryEndpointsPaidIsTrue : atomic369InventoryEndpointsPaid ≡ true
    individualAtomIdentityTransportPaid : Bool
    individualAtomIdentityTransportPaidIsFalse : individualAtomIdentityTransportPaid ≡ false
    molecularBondRearrangementPaid : Bool
    molecularBondRearrangementPaidIsTrue : molecularBondRearrangementPaid ≡ true
    fibreCreatesExactQuantumTrajectory : Bool
    fibreCreatesExactQuantumTrajectoryIsFalse : fibreCreatesExactQuantumTrajectory ≡ false
    fibreCreatesMonsterAction : Bool
    fibreCreatesMonsterActionIsFalse : fibreCreatesMonsterAction ≡ false

open HyperformBoundary public

canonicalHyperformBoundary : HyperformBoundary
canonicalHyperformBoundary =
  hyperformBoundary
    true refl
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
