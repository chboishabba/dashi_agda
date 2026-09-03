module DASHI.Culture.MissingDeceasedFusionSpaceDomainBridgeReconciliationExact where

open import DASHI.Core.Prelude

import DASHI.Core.ProgrammeMediatedTechnicalDomainBridgeBidiExact as B
import DASHI.Culture.MissingDeceasedTechnicalDependencyHypergraphExact as M
import DASHI.Culture.NASAFusionPlasmaSpacePropulsionBridgeExact as N

------------------------------------------------------------------------
-- RECONCILIATION OF THE EARLIER BROAD-ADJACENCY SNAPSHOT.
--
-- The earlier fixture correctly refused to promote
--
--   magnetic reconnection / fusion plasma  <->  space systems
--
-- from broad similarity alone.  The NASA programme receipts now establish a
-- narrower but genuine technology-domain bridge:
--
--   fusion / magnetized plasma / FRC <-> spacecraft propulsion + power.
--
-- This does not retroactively create a person-to-programme edge for Loureiro,
-- LeBlanc, or any other named person.
------------------------------------------------------------------------

record PlasmaSpaceReconciliation : Set₁ where
  constructor plasma-space-reconciliation
  field
    oldAdjacency : Set
    promotedProgrammeBridge : B.PromotedTechnicalDomainBridge

    fusionPlasmaToSpacePropulsionNowProgrammeBacked : Bool
    fusionPlasmaToSpacePropulsionNowProgrammeBackedIsTrue :
      fusionPlasmaToSpacePropulsionNowProgrammeBacked ≡ true

    magneticReconnectionSpecificallyIsNASAPropulsionMechanism : Bool
    magneticReconnectionSpecificallyIsNASAPropulsionMechanismIsFalse :
      magneticReconnectionSpecificallyIsNASAPropulsionMechanism ≡ false

    loureiroWorkedOnNASAFusionPropulsionFromBridge : Bool
    loureiroWorkedOnNASAFusionPropulsionFromBridgeIsFalse :
      loureiroWorkedOnNASAFusionPropulsionFromBridge ≡ false

    leblancWorkedOnNASAFusionPropulsionFromBridge : Bool
    leblancWorkedOnNASAFusionPropulsionFromBridgeIsFalse :
      leblancWorkedOnNASAFusionPropulsionFromBridge ≡ false

    loureiroLeBlancSharedProgrammeFromBridge : Bool
    loureiroLeBlancSharedProgrammeFromBridgeIsFalse :
      loureiroLeBlancSharedProgrammeFromBridge ≡ false

canonicalPlasmaSpaceReconciliation : PlasmaSpaceReconciliation
canonicalPlasmaSpaceReconciliation =
  plasma-space-reconciliation
    (M.H.CandidateDomainAdjacency)
    N.fusionToPropulsionPromoted
    true refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- BIDI cross-pollination:
--
-- Forward:
--   NASA programme evidence upgrades the domain topology used by the roster
--   hypergraph.
--
-- Reverse:
--   the roster consumer now asks for a much sharper next receipt if a
--   person-level connection is claimed: named programme participation for the
--   named person, rather than another generic fusion/space citation.
------------------------------------------------------------------------

record PersonBridgeAcquisitionObligations : Set where
  constructor person-bridge-acquisition-obligations
  field
    genericFusionSpaceProgrammeReceiptStillNeeded : Bool
    genericFusionSpaceProgrammeReceiptStillNeededIsFalse :
      genericFusionSpaceProgrammeReceiptStillNeeded ≡ false

    namedPersonProgrammeReceiptNeeded : Bool
    namedPersonProgrammeReceiptNeededIsTrue :
      namedPersonProgrammeReceiptNeeded ≡ true

    namedProgrammeOrContractIdentifierNeeded : Bool
    namedProgrammeOrContractIdentifierNeededIsTrue :
      namedProgrammeOrContractIdentifierNeeded ≡ true

canonicalPersonBridgeAcquisitionObligations : PersonBridgeAcquisitionObligations
canonicalPersonBridgeAcquisitionObligations =
  person-bridge-acquisition-obligations false refl true refl true refl
