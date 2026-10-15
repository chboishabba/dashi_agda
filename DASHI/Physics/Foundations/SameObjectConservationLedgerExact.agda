{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.SameObjectConservationLedgerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ReopenableConsumerInterventionKernelExact as Core

------------------------------------------------------------------------
-- SAME-OBJECT CONSERVATION LEDGER
--
-- DASHI synthesis owner.  This module does not assert any domain-specific
-- conservation law.  It types the bookkeeping surface on which a domain may
-- later supply a physical-law and same-object identification receipt.
------------------------------------------------------------------------

record SameObjectInterval : Set where
  constructor same-object-interval
  field
    startApparatusId : String
    endApparatusId : String
    startStateId : String
    endStateId : String
    sameApparatusIdentity : startApparatusId ≡ endApparatusId

open SameObjectInterval public

canonicalSameObjectInterval : SameObjectInterval
canonicalSameObjectInterval =
  same-object-interval
    "fixture-apparatus" "fixture-apparatus" "t0" "t1" refl

data ChannelStatus : Set where
  admitted : ChannelStatus
  unresolved : ChannelStatus
  excludedByReceipt : ChannelStatus

record AdmittedChannelSet : Set where
  constructor admitted-channel-set
  field
    matterChannel : ChannelStatus
    fieldChannel : ChannelStatus
    boundaryFluxChannel : ChannelStatus
    sourceChannel : ChannelStatus
    nuisanceChannel : ChannelStatus
    unresolvedChannelsAreNotZero : Bool

open AdmittedChannelSet public

canonicalAdmittedChannels : AdmittedChannelSet
canonicalAdmittedChannels =
  admitted-channel-set admitted admitted unresolved admitted unresolved true

record EnergyLedger : Set where
  constructor energy-ledger
  field
    interval : SameObjectInterval
    channels : AdmittedChannelSet
    observedEnergyChange : String
    admittedWork : String
    admittedHeat : String
    admittedBoundaryFlux : String
    residualDefinition : String
    domainConservationReceiptRequired : Bool

open EnergyLedger public

record MomentumLedger : Set where
  constructor momentum-ledger
  field
    interval : SameObjectInterval
    channels : AdmittedChannelSet
    observedMomentumChange : String
    admittedMatterMomentum : String
    admittedFieldMomentum : String
    admittedBoundaryMomentumFlux : String
    admittedExternalImpulse : String
    residualDefinition : String
    domainConservationReceiptRequired : Bool

open MomentumLedger public

record EntropyLedger : Set where
  constructor entropy-ledger
  field
    interval : SameObjectInterval
    channels : AdmittedChannelSet
    observedEntropyChange : String
    admittedEntropyTransport : String
    admittedEntropyProduction : String
    residualDefinition : String
    equilibriumNotAssumed : Bool

open EntropyLedger public

record ChargeLedger : Set where
  constructor charge-ledger
  field
    interval : SameObjectInterval
    channels : AdmittedChannelSet
    observedChargeChange : String
    admittedCurrentFlux : String
    admittedChargeSource : String
    residualDefinition : String
    domainContinuityReceiptRequired : Bool

open ChargeLedger public

record ResidualLedger : Set where
  constructor residual-ledger
  field
    interval : SameObjectInterval
    channels : AdmittedChannelSet
    observedQuantity : String
    accountedQuantity : String
    residualQuantity : String
    residualRelativeToDeclaredChannels : Bool
    unresolvedChannelBlocksClosure : Bool

open ResidualLedger public

canonicalEnergyLedger : EnergyLedger
canonicalEnergyLedger =
  energy-ledger canonicalSameObjectInterval canonicalAdmittedChannels
    "delta-E-observed" "W-admitted" "Q-admitted" "Phi-E-admitted"
    "R_E = observed - admitted channels" true

canonicalMomentumLedger : MomentumLedger
canonicalMomentumLedger =
  momentum-ledger canonicalSameObjectInterval canonicalAdmittedChannels
    "delta-P-observed" "delta-P-matter" "delta-P-field"
    "Phi-P-boundary" "I-external"
    "R_P = observed - admitted channels" true

canonicalEntropyLedger : EntropyLedger
canonicalEntropyLedger =
  entropy-ledger canonicalSameObjectInterval canonicalAdmittedChannels
    "delta-S-observed" "S-transport" "S-produced"
    "R_S = observed - admitted channels" true

canonicalChargeLedger : ChargeLedger
canonicalChargeLedger =
  charge-ledger canonicalSameObjectInterval canonicalAdmittedChannels
    "delta-Q-observed" "J-boundary" "Q-source"
    "R_Q = observed - admitted channels" true

canonicalResidualLedger : ResidualLedger
canonicalResidualLedger =
  residual-ledger canonicalSameObjectInterval canonicalAdmittedChannels
    "observed" "accounted" "residual" true true

------------------------------------------------------------------------
-- FINITE EXACT BOOKKEEPING FIXTURE
--
-- A newly admitted nuisance channel changes the residual rather than being
-- silently treated as zero.  Natural-number magnitudes are sufficient for the
-- finite bookkeeping witness; no physical sign convention is inferred.
------------------------------------------------------------------------

finiteObserved : Nat
finiteObserved = 10

finiteCoarseAccounted : Nat
finiteCoarseAccounted = 6

finiteAddedNuisance : Nat
finiteAddedNuisance = 3

coarseFiniteResidual : Nat
coarseFiniteResidual = 4

refinedFiniteResidual : Nat
refinedFiniteResidual = 1

coarseFiniteLedgerCloses :
  finiteObserved ≡ finiteCoarseAccounted + coarseFiniteResidual
coarseFiniteLedgerCloses = refl

refinedFiniteLedgerCloses :
  finiteObserved
    ≡ (finiteCoarseAccounted + finiteAddedNuisance) + refinedFiniteResidual
refinedFiniteLedgerCloses = refl

coarseFiniteResidualIsFour : coarseFiniteResidual ≡ 4
coarseFiniteResidualIsFour = refl

refinedFiniteResidualIsOne : refinedFiniteResidual ≡ 1
refinedFiniteResidualIsOne = refl

finiteResidualRefinementDistinguishes :
  coarseFiniteResidual ≡ refinedFiniteResidual → ⊥
finiteResidualRefinementDistinguishes ()

------------------------------------------------------------------------
-- CONSUMER-RELATIVE COLLISION
--
-- Same coarse readout, different nuisance/consumer state.  This is a DASHI
-- finite fixture showing why a coarse measurement cannot silently close a
-- consumer that depends on an erased coordinate.
------------------------------------------------------------------------

data FixtureWorld : Set where
  thermalWorld : FixtureWorld
  forceWorld : FixtureWorld

coarseObserved : FixtureWorld → Bool
coarseObserved thermalWorld = true
coarseObserved forceWorld = true

consumerRelevant : FixtureWorld → Bool
consumerRelevant thermalWorld = false
consumerRelevant forceWorld = true

consumerDistinguishesFixture :
  consumerRelevant thermalWorld ≡ consumerRelevant forceWorld → ⊥
consumerDistinguishesFixture ()

coarseObserverDefect :
  Core.ConsumerDescentDefect coarseObserved consumerRelevant
coarseObserverDefect =
  Core.consumerDescentDefect
    thermalWorld
    forceWorld
    refl
    consumerDistinguishesFixture

record ConservationLedgerBoundary : Set where
  constructor conservation-ledger-boundary
  field
    ledgersRemainSeparate : Bool
    residualNeedsDeclaredChannels : Bool
    unresolvedChannelsAreNotZeroByDefault : Bool
    domainLawMustBeSuppliedByAdapter : Bool
    coarseObservationNeedNotDetermineConsumer : Bool
    sameObjectIdentityNeedsEqualityReceipt : Bool
    admittedNuisanceCanChangeResidual : Bool

open ConservationLedgerBoundary public

canonicalConservationLedgerBoundary : ConservationLedgerBoundary
canonicalConservationLedgerBoundary =
  conservation-ledger-boundary true true true true true true true
