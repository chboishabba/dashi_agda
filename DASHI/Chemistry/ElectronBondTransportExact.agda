module DASHI.Chemistry.ElectronBondTransportExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Chemistry.AtomicMolecularReactionLineageHyperfabricExact as Lineage

------------------------------------------------------------------------
-- ELECTRON / BOND TRANSPORT
--
-- Charge balance, electron-equivalent transfer and bond rearrangement are
-- related but nonidentical obligations.  Because electrons are indistinguish-
-- able fermions, these receipts track reducing equivalents, occupations,
-- density/current or source->sink carrier changes, not persistent named
-- individual particles through arbitrary many-body states.
------------------------------------------------------------------------

data ElectronTransferKind : Set where
  oneElectronTransfer : ElectronTransferKind
  pairedElectronTransfer : ElectronTransferKind
  hydrideTransfer : ElectronTransferKind
  protonCoupledElectronTransfer : ElectronTransferKind
  delocalisationRedistribution : ElectronTransferKind
  electrodeExchange : ElectronTransferKind
  unresolvedElectronTransfer : ElectronTransferKind

record ElectronTransferReceipt : Set where
  constructor electronTransferReceipt
  field
    transition : Chemistry.Transition
    electron : Lineage.ElectronLineage
    kind : ElectronTransferKind
    electronEquivalentCount : Nat
    donorCarrierReference : String
    acceptorCarrierReference : String
    donorOxidationStateReference : String
    acceptorReductionStateReference : String
    orbitalOrCofactorReference : String
    protonCouplingReference : String
    externalReservoirReference : String
    conservationReference : String
    evidenceReference : String

open ElectronTransferReceipt public

data BondChangeKind : Set where
  bondFormation : BondChangeKind
  bondCleavage : BondChangeKind
  bondOrderIncrease : BondChangeKind
  bondOrderDecrease : BondChangeKind
  coordinationFormation : BondChangeKind
  coordinationLoss : BondChangeKind
  geometryOnlyReorganisation : BondChangeKind

record BondChangeReceipt : Set where
  constructor bondChangeReceipt
  field
    transition : Chemistry.Transition
    kind : BondChangeKind
    atomLineageA : String
    atomLineageB : String
    beforeBondReference : String
    afterBondReference : String
    beforeGeometryReference : String
    afterGeometryReference : String
    electronicCauseReference : String
    energeticReference : String
    evidenceReference : String

open BondChangeReceipt public

record ReactionElectronicAudit : Set₁ where
  constructor reactionElectronicAudit
  field
    transition : Chemistry.Transition
    electronTransfers : List ElectronTransferReceipt
    bondChanges : List BondChangeReceipt
    formalChargeBalanceReference : String
    oxidationStateBalanceReference : String
    protonBalanceReference : String
    atomMappingReference : String
    electronMappingReference : String
    unresolvedElectronicResidualReference : String
    computationalOrExperimentalValidationReference : String

open ReactionElectronicAudit public

record ElectronBondTransportBoundary : Set where
  constructor electronBondTransportBoundary
  field
    stoichiometricBalanceDeterminesElectronTransport : Bool
    stoichiometricBalanceDeterminesElectronTransportIsFalse :
      stoichiometricBalanceDeterminesElectronTransport ≡ false

    chargeBalanceDeterminesBondChange : Bool
    chargeBalanceDeterminesBondChangeIsFalse :
      chargeBalanceDeterminesBondChange ≡ false

    persistentIndividualElectronIdentityTracked : Bool
    persistentIndividualElectronIdentityTrackedIsFalse :
      persistentIndividualElectronIdentityTracked ≡ false

    electronEquivalentOrDensityFlowTrackable : Bool
    electronEquivalentOrDensityFlowTrackableIsTrue :
      electronEquivalentOrDensityFlowTrackable ≡ true

    oxidationStateBookkeepingEqualsLiteralElectronTrajectory : Bool
    oxidationStateBookkeepingEqualsLiteralElectronTrajectoryIsFalse :
      oxidationStateBookkeepingEqualsLiteralElectronTrajectory ≡ false

    electronTransferCanOccurWithNuclearIdentityPreserved : Bool
    electronTransferCanOccurWithNuclearIdentityPreservedIsTrue :
      electronTransferCanOccurWithNuclearIdentityPreserved ≡ true

    bondChangeCanAlterGeometryWithoutChangingAtomicIdentity : Bool
    bondChangeCanAlterGeometryWithoutChangingAtomicIdentityIsTrue :
      bondChangeCanAlterGeometryWithoutChangingAtomicIdentity ≡ true

    externalElectronReservoirMustBeExplicit : Bool
    externalElectronReservoirMustBeExplicitIsTrue :
      externalElectronReservoirMustBeExplicit ≡ true

    exactQuantumElectronTrajectoryPromotedFromFormalBookkeeping : Bool
    exactQuantumElectronTrajectoryPromotedFromFormalBookkeepingIsFalse :
      exactQuantumElectronTrajectoryPromotedFromFormalBookkeeping ≡ false

open ElectronBondTransportBoundary public

canonicalElectronBondTransportBoundary : ElectronBondTransportBoundary
canonicalElectronBondTransportBoundary =
  electronBondTransportBoundary
    false refl
    false refl
    false refl
    true refl
    false refl
    true refl
    true refl
    true refl
    false refl
