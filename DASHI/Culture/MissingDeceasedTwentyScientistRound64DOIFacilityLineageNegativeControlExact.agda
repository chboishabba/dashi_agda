module DASHI.Culture.MissingDeceasedTwentyScientistRound64DOIFacilityLineageNegativeControlExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- ROUND 64: DOI-BEARING FACILITY-LINEAGE NEGATIVE CONTROL
--
-- Real DOIs strengthen carrier identity. They do not widen proposition scope.
-- The DARHT Capability eXpansion strategy co-names several people who also
-- appear in the later MPTL technical lineage, but the strategy is a broad
-- facility-level carrier rather than an exact MPTL object receipt.
------------------------------------------------------------------------

dcxStrategyDOISource : Source.AttributedSource
dcxStrategyDOISource = Source.mkDOISource
  "Howard Bender et al.; including Joaquin Campos, Carl Ekdahl, Michael Jaworski, Martin Schulze and collaborators"
  "The Dual-Axis Radiographic Hydrodynamic Test Facility Capability eXpansion (DCX) Strategy"
  "Los Alamos National Laboratory / OSTI report LA-UR-22-30202"
  "2022"
  "10.2172/1898347"
  "https://doi.org/10.2172/1898347"
  Source.governmentSource
  "Pays a DOI-bearing DARHT facility capability-expansion strategy and coauthor surface. It is facility-level context; it does not by itself identify the later MPTL object, its review, its achromat revision, or a retained-person crossing."
  Source.publicAttribution

dcxEarlierStrategyDOISource : Source.AttributedSource
dcxEarlierStrategyDOISource = Source.mkDOISource
  "Howard Bender III et al.; including Joshua Coleman, Joaquin Campos, Carl Ekdahl Jr., Michael Jaworski, Martin Schulze and collaborators"
  "The Dual-Axis Radiographic Hydrodynamic Test Facility Capability Expansion (DCX) Strategy"
  "Los Alamos National Laboratory / OSTI report"
  "2022"
  "10.2172/1890956"
  "https://doi.org/10.2172/1890956"
  Source.governmentSource
  "Pays a DOI-bearing DARHT facility strategy carrier. It is retained separately because DOI/version identity matters; title similarity does not collapse distinct report records."
  Source.publicAttribution

doiStrengthensCarrierIdentityNotClaimScope : Bool
doiStrengthensCarrierIdentityNotClaimScope = true

facilityLevelCoauthoringDoesNotPayMPTLSameObject : Bool
facilityLevelCoauthoringDoesNotPayMPTLSameObject = true

mptlAuthorsMayAppearInDARHTLineageWithoutMPTLReceipt : Bool
mptlAuthorsMayAppearInDARHTLineageWithoutMPTLReceipt = true

doiCannotBridgeObjectGranularity : Bool
doiCannotBridgeObjectGranularity = true

sameFacilityFutureStrategyDoesNotEqualLaterEngineeringRevision : Bool
sameFacilityFutureStrategyDoesNotEqualLaterEngineeringRevision = true

sameAuthorAcrossFacilityAndObjectDoesNotTransferEveryClaim : Bool
sameAuthorAcrossFacilityAndObjectDoesNotTransferEveryClaim = true

versionedDOIRecordsMustRemainDistinct : Bool
versionedDOIRecordsMustRemainDistinct = true

round64H2PaidCount : Nat
round64H2PaidCount = 0

round64H3PaidCount : Nat
round64H3PaidCount = 0

round64Reading : String
round64Reading = "The DARHT DCX strategy provides DOI-bearing facility-level provenance and coauthor lineage for several people who later appear on MPTL technical carriers. That improves identity and chronology but cannot widen the proposition to exact MPTL participation. A DOI identifies a carrier; it does not bridge facility -> programme -> exact object -> revision -> retained-person crossing. The two acquired DCX DOI records are retained separately rather than collapsed by title similarity. H2/H3 remain unpaid."
