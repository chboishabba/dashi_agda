module DASHI.Chemistry.AtomicMolecularReactionLineageHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact as Atomic369
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ChemistryHyperfibreBridgeExact as Chemistry369
import DASHI.Biology.Molecular.MolecularAssemblyBoundary as Molecular
import DASHI.Biology.Molecular.MolecularConstrainedMinimizerBridge as Geometry
import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Chemistry.AdmissibleReactionTransitionBridgeExact as Reaction
import DASHI.Core.ConsumerRelativeCoarseGrainingBidiExact as Coarse

------------------------------------------------------------------------
-- ATOMIC -> MOLECULAR -> REACTION LINEAGE HYPERFABRIC
--
-- Existing owners already provide the atomic generator, molecular assembly,
-- constrained geometry and typed reaction kernel.  This owner contributes the
-- missing proof-relevant lineage seam: persistent nuclear/atomic identity,
-- electron-equivalent/redox transport, molecule membership, reaction
-- product/byproduct ancestry and observer-relative residuals are distinct.
--
-- Important physics boundary: electrons are indistinguishable fermions.  An
-- ElectronLineage below is therefore an operational carrier for electron
-- equivalents, occupation/redox change or calculated density flow.  It is not
-- a claim that an experimentally meaningful named individual electron persists
-- through arbitrary many-body states.
------------------------------------------------------------------------

record AtomicLineage : Set where
  constructor atomicLineage
  field
    lineageId : String
    atomicIndex : Atomic369.AtomicIndex
    atomicStateReference : String
    molecularMembershipReference : String
    isotopeReference : String
    sourceProvenanceReference : String

open AtomicLineage public

record NuclearIdentityTransport
    (source target : AtomicLineage) : Set where
  constructor nuclearIdentityTransport
  field
    sameProtonNumber :
      Atomic369.protonNumber (atomicIndex source)
      ≡ Atomic369.protonNumber (atomicIndex target)
    sameNeutronNumber :
      Atomic369.neutronNumber (atomicIndex source)
      ≡ Atomic369.neutronNumber (atomicIndex target)
    nonNuclearChemistryReference : String
    persistentLineageReference : String

open NuclearIdentityTransport public

------------------------------------------------------------------------
-- Electron-equivalent / occupation lineage.
------------------------------------------------------------------------

record ElectronLineage : Set where
  constructor electronLineage
  field
    electronLineageId : String
    sourceCarrierReference : String
    targetCarrierReference : String
    initialElectronicStateReference : String
    finalElectronicStateReference : String
    spinOrOccupancyReference : String
    transferMechanismReference : String
    measurementOrCalculationReference : String

open ElectronLineage public

------------------------------------------------------------------------
-- A molecular lineage state carries upstream atom/electronic identities in
-- addition to molecule/bond/geometry/stereo/environment coordinates.
------------------------------------------------------------------------

record MolecularLineageState : Set where
  constructor molecularLineageState
  field
    moleculeId : String
    atoms : List AtomicLineage
    electrons : List ElectronLineage
    bondGraphReference : String
    geometryReference : String
    stereochemistryReference : String
    formalChargeReference : String
    environmentReference : String
    assemblyWitnessReference : String
    observationalIdentityReference : String

open MolecularLineageState public

record MolecularGeometryLineageReceipt : Set where
  constructor molecularGeometryLineageReceipt
  field
    moleculeReference : String
    atomicInventoryReference : String
    valenceReference : String
    admissibleBondReference : String
    constrainedMinimizerReference : String
    geometryReference : String
    stereochemistryReference : String
    environmentReference : String
    geometryValidationReference : String

open MolecularGeometryLineageReceipt public

------------------------------------------------------------------------
-- Reaction transport: products and byproducts are separate molecular lineage
-- states.  Atom and electron-equivalent transport are separate obligations.
------------------------------------------------------------------------

record ReactionLineageTransport : Set₁ where
  constructor reactionLineageTransport
  field
    transition : Chemistry.Transition
    reactantStates : List MolecularLineageState
    productStates : List MolecularLineageState
    byproductStates : List MolecularLineageState
    nuclearTransports : List String
    electronTransports : List ElectronLineage
    bondChangeReference : String
    geometryChangeReference : String
    chargeAccountingReference : String
    stoichiometryReference : String
    compartmentReference : String
    reactionEnablementReference : String
    rateOrEnergeticsReference : String
    observationReference : String
    provenanceReference : String

open ReactionLineageTransport public

------------------------------------------------------------------------
-- Cross-scale observer receipt.
------------------------------------------------------------------------

record LineageObserverReceipt : Set where
  constructor lineageObserverReceipt
  field
    fineStateReference : String
    coarseObservationReference : String
    declaredConsumerReference : String
    retainedCoordinatesReference : String
    collapsedCoordinatesReference : String
    relativeFineResidualReference : String
    collisionSearchReference : String
    refinementReference : String

open LineageObserverReceipt public

------------------------------------------------------------------------
-- Existing-owner anchors.  These are reused, not reimplemented.
------------------------------------------------------------------------

atomicChemistryBoundary : Chemistry369.AtomicChemistryCrossPollinationBoundary
atomicChemistryBoundary = Chemistry369.canonicalAtomicChemistryCrossPollinationBoundary

reactionBoundary : Reaction.ReactionMDLBoundary
reactionBoundary = Reaction.canonicalReactionMDLBoundary

coarseBoundary : Coarse.ConsumerRelativeCoarseGrainingBoundary
coarseBoundary = Coarse.canonicalConsumerRelativeCoarseGrainingBoundary

molecularAssemblySurface : Set₁
molecularAssemblySurface = Molecular.MolecularAssemblySystem

------------------------------------------------------------------------
-- Max-cut non-collapse boundary.
------------------------------------------------------------------------

record AtomicMolecularReactionLineageBoundary : Set where
  constructor atomicMolecularReactionLineageBoundary
  field
    everyAtomicCarrierUses369AtomicIndex : Bool
    everyAtomicCarrierUses369AtomicIndexIsTrue :
      everyAtomicCarrierUses369AtomicIndex ≡ true

    nuclearIdentityTransportIsDistinctFromElectronTransport : Bool
    nuclearIdentityTransportIsDistinctFromElectronTransportIsTrue :
      nuclearIdentityTransportIsDistinctFromElectronTransport ≡ true

    electronLineageMeansPersistentIndividualFermionIdentity : Bool
    electronLineageMeansPersistentIndividualFermionIdentityIsFalse :
      electronLineageMeansPersistentIndividualFermionIdentity ≡ false

    electronEquivalentOrDensityTransportIsTrackable : Bool
    electronEquivalentOrDensityTransportIsTrackableIsTrue :
      electronEquivalentOrDensityTransportIsTrackable ≡ true

    atomConservationProvesElectronTransport : Bool
    atomConservationProvesElectronTransportIsFalse :
      atomConservationProvesElectronTransport ≡ false

    molecularFormulaDeterminesBondGeometry : Bool
    molecularFormulaDeterminesBondGeometryIsFalse :
      molecularFormulaDeterminesBondGeometry ≡ false

    geometryRequiresIndependentAssemblyOrMinimizerWitness : Bool
    geometryRequiresIndependentAssemblyOrMinimizerWitnessIsTrue :
      geometryRequiresIndependentAssemblyOrMinimizerWitness ≡ true

    sameMoleculeLabelDeterminesSameLineage : Bool
    sameMoleculeLabelDeterminesSameLineageIsFalse :
      sameMoleculeLabelDeterminesSameLineage ≡ false

    stoichiometricBalanceDeterminesReactionMechanism : Bool
    stoichiometricBalanceDeterminesReactionMechanismIsFalse :
      stoichiometricBalanceDeterminesReactionMechanism ≡ false

    productsRetainReactantLineageCoordinates : Bool
    productsRetainReactantLineageCoordinatesIsTrue :
      productsRetainReactantLineageCoordinates ≡ true

    byproductsRemainFirstClassLineageOutputs : Bool
    byproductsRemainFirstClassLineageOutputsIsTrue :
      byproductsRemainFirstClassLineageOutputs ≡ true

    coarseObserverEqualityImpliesFineIdentity : Bool
    coarseObserverEqualityImpliesFineIdentityIsFalse :
      coarseObserverEqualityImpliesFineIdentity ≡ false

    fineResidualRemainsReopenable : Bool
    fineResidualRemainsReopenableIsTrue :
      fineResidualRemainsReopenable ≡ true

    empiricalPromotionFromStructureAlone : Bool
    empiricalPromotionFromStructureAloneIsFalse :
      empiricalPromotionFromStructureAlone ≡ false

open AtomicMolecularReactionLineageBoundary public

canonicalAtomicMolecularReactionLineageBoundary :
  AtomicMolecularReactionLineageBoundary
canonicalAtomicMolecularReactionLineageBoundary =
  atomicMolecularReactionLineageBoundary
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
    true refl
    false refl
    false refl
    true refl
    true refl
    false refl
    true refl
    false refl
