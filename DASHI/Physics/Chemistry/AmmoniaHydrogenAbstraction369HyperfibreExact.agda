module DASHI.Physics.Chemistry.AmmoniaHydrogenAbstraction369HyperfibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List)
import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as Atomic369
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ChemistryHyperfibreBridgeExact as Fibre
import DASHI.Physics.Chemistry.AmmoniaHydrogenAbstractionMechanismExact as Mechanism

------------------------------------------------------------------------
-- CONCRETE 369 HYPERFIBRE FOR 14NH3 + 1H -> 14NH2 + 1H2
--
-- Unlike the generic bridge, this module actually inhabits the fibre at a
-- source and target time.  The atomic carrier is literally the existing
-- Atomic369.AtomicIndex inventory.  Molecular/reaction identity is then welded
-- separately, preserving the repo's no-collapse rule.
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
    (λ t → "AtomicPeriodicTable369GenerativeExact literal AtomicIndex inventory at " ++ timeLabel t)
    (λ t → "source-backed molecular identity at " ++ timeLabel t)
    (λ t → "Espinosa-Garcia/Corchado 2010 + Corchado/Espinosa-Garcia/Yang 2011 reaction identity/mechanism at " ++ timeLabel t)
    (λ _ → "no industrial promotion in this microscopic fixture")
    (λ _ → "NH3-H-abstraction-369-hyperfibre-v1")
  where
    timeLabel : ReactionTime → String
    timeLabel beforeCollision = "beforeCollision"
    timeLabel afterReaction = "afterReaction"

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
    "same 14N + four 1H AtomicIndex inventory"
    "NH2 + H2 target molecular state"
    "target state for PES-2009 abstraction path"
    "not industrial"

abstractionTransport : Fibre.ChemistryFibreTransport sourceFibre targetFibre
abstractionTransport =
  Fibre.chemistryFibreTransport
    "separatedReactants -> entranceApproach -> saddleRegion -> exitSeparation -> separatedProducts"
    "same literal 14N + four 1H AtomicIndex inventory; atom identities conserved while bonding changes"
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
    atomicIdentityTransportPaid : Bool
    atomicIdentityTransportPaidIsTrue : atomicIdentityTransportPaid ≡ true
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
    true refl
    false refl
    false refl
