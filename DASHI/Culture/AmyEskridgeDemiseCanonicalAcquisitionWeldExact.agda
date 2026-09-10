module DASHI.Culture.AmyEskridgeDemiseCanonicalAcquisitionWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.EvidenceAcquisitionSelectiveReopeningExact as Acquisition
import DASHI.Culture.AmyEskridgeAcquisitionProofSearchExact as Search
import DASHI.Culture.AmyEskridgeDemiseCircumstancesSnowballExact as Demise

------------------------------------------------------------------------
-- AMY ESKRIDGE MEMORIAL: DEMISE -> CANONICAL ACQUISITION WELD
--
-- The demise snowball should not maintain a second string-shaped acquisition
-- system beside AmyEskridgeAcquisitionProofSearchExact.  This adapter points
-- each forensic atom at the already-canonical AcquisitionTarget and obligation.
-- Acquisition may occur out of order; evidentiary promotion remains governed by
-- the existing selective-reopening dependency graph.
------------------------------------------------------------------------

record DemiseAcquisitionWeld : Set where
  constructor demise-acquisition-weld
  field
    atom : Demise.DemiseSnowballAtom
    target : Acquisition.AcquisitionTarget
    obligation : Acquisition.AcquisitionObligation target
    atomIsStillNotPubliclyLocated :
      Demise.inspectionStatus atom ≡ Demise.notPubliclyLocated
    atomOpensAcquisitionObligation :
      Demise.evidentiaryEffect atom ≡ Demise.opensAcquisitionObligation
    sameCanonicalAcquisitionBranch : Bool
    sameCanonicalAcquisitionBranchIsTrue :
      sameCanonicalAcquisitionBranch ≡ true

open DemiseAcquisitionWeld public

autopsyCanonicalWeld : DemiseAcquisitionWeld
autopsyCanonicalWeld = demise-acquisition-weld
  Demise.autopsyAcquisitionAtom
  Search.autopsyTarget
  Search.autopsyObligation
  refl refl true refl

toxicologyCanonicalWeld : DemiseAcquisitionWeld
toxicologyCanonicalWeld = demise-acquisition-weld
  Demise.toxicologyAcquisitionAtom
  Search.toxicologyTarget
  Search.toxicologyObligation
  refl refl true refl

policeCanonicalWeld : DemiseAcquisitionWeld
policeCanonicalWeld = demise-acquisition-weld
  Demise.policeAcquisitionAtom
  Search.policeReportTarget
  Search.policeReportObligation
  refl refl true refl

------------------------------------------------------------------------
-- Ballistics/GSR was already a canonical acquisition target and dependency
-- producer, but the demise snowball lacked its direct atom.  Construct it from
-- the canonical target name so no second locator string is introduced.
------------------------------------------------------------------------

ballisticsAcquisitionAtom : Demise.DemiseSnowballAtom
ballisticsAcquisitionAtom =
  Demise.demise-snowball-atom
    Demise.primaryForensicRecord
    Demise.reportedMechanismOfDeath
    (Acquisition.targetName Search.ballisticsTarget)
    "No authenticated public firearm / ballistics / GSR carrier has been located in the current public-source review; lawful primary-record acquisition remains open."
    Demise.notPubliclyLocated
    Demise.opensAcquisitionObligation
    true false false

ballisticsCanonicalWeld : DemiseAcquisitionWeld
ballisticsCanonicalWeld = demise-acquisition-weld
  ballisticsAcquisitionAtom
  Search.ballisticsTarget
  Search.ballisticsObligation
  refl refl true refl

------------------------------------------------------------------------
-- The canonical acquisition graph already owns the reopening semantics.
------------------------------------------------------------------------

autopsyStillReopensDeathMechanismOnlyThroughDeclaredEdge :
  Acquisition.SelectiveAcquisitionReopening
    Search.eskridgeAcquisitionGraph
    Search.autopsyArtifact
    Search.deathMechanismAssessment
autopsyStillReopensDeathMechanismOnlyThroughDeclaredEdge =
  Search.autopsyReopensDeathMechanism

record DemiseCanonicalAcquisitionBoundary : Set where
  constructor demise-canonical-acquisition-boundary
  field
    demiseAtomCreatesSecondAcquisitionOntology : Bool
    atomTextMayReplaceCanonicalTargetIdentity : Bool
    autopsyUsesCanonicalTarget : Bool
    toxicologyUsesCanonicalTarget : Bool
    policeUsesCanonicalTarget : Bool
    ballisticsUsesCanonicalTarget : Bool
    acquisitionAutomaticallyProvesReportedManner : Bool
    acquisitionAutomaticallyProvesCulprit : Bool
    forensicAcquisitionPaysScientificMechanismLeaf : Bool
    acquiredRecordMayReopenOnlyDeclaredConsumers : Bool

open DemiseCanonicalAcquisitionBoundary public

canonicalDemiseCanonicalAcquisitionBoundary : DemiseCanonicalAcquisitionBoundary
canonicalDemiseCanonicalAcquisitionBoundary =
  demise-canonical-acquisition-boundary
    false false
    true true true true
    false false false true
