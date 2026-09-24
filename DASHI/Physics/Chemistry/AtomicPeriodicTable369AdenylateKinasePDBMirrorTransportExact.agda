module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePDBMirrorTransportExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePDBAtomisticFixtureExact as Fixture

------------------------------------------------------------------------
-- PROVENANCE-ONLY MIRROR TRANSPORT LANE
--
-- This owner exists to unblock executable acquisition when the canonical
-- wwPDB/RCSB byte endpoint is transport-inaccessible in the current runtime.
-- A mirror is retained as a separately identified transport manifestation only.
-- It does not replace the PDB deposition authority and does not pay canonical
-- archive-byte identity.
------------------------------------------------------------------------

record PDBMirrorTransportCandidate : Set where
  constructor pdb-mirror-transport-candidate
  field
    pdbLabel : String
    pdbDepositionDOI : String
    authorityCoordinateReference : String
    mirrorRepository : String
    mirrorPath : String
    mirrorObjectURL : String
    mirrorGitBlobSha : String
    mirrorGitBlobHashKind : String
    mirrorObjectObserved : Bool
    completeCoordinatePayloadClaimedByMirror : Bool
    canonicalArchiveByteEqualityObserved : Bool
    sourceByteSha256Pinned : Bool
    scientificAuthorityPromotedFromMirror : Bool
    interpretation : String
open PDBMirrorTransportCandidate public

------------------------------------------------------------------------
-- These exact GitHub object identifiers were returned by the GitHub contents
-- API during this acquisition tranche. They identify the mirror objects only.
-- They are not SHA-256 receipts for the PDB bytes and are not evidence that the
-- mirror bytes equal the current canonical wwPDB archive manifestation.
------------------------------------------------------------------------

open4AKEMirror : PDBMirrorTransportCandidate
open4AKEMirror = pdb-mirror-transport-candidate
  "4AKE"
  (Fixture.pdbDepositionDOI Fixture.open4AKEManifestation)
  "canonical PDB authority remains the 4AKE deposition identity and Fixture.open4AKEManifestation"
  "YueHuLab/LieRMSD"
  "4AKE.pdb"
  "https://github.com/YueHuLab/LieRMSD/blob/main/4AKE.pdb"
  "a6990f8befb52ca25ca0b65674e0861f53dd7ee5"
  "GitHub blob SHA returned by repository contents API; transport-object identity only"
  true true false false false
  "candidate transport manifestation for executing the AdK PDB->CV script while canonical archive transport is unavailable; must be content-hashed after materialization and later compared with canonical archive bytes"

closed1AKEMirror : PDBMirrorTransportCandidate
closed1AKEMirror = pdb-mirror-transport-candidate
  "1AKE"
  (Fixture.pdbDepositionDOI Fixture.closed1AKEManifestation)
  "canonical PDB authority remains the 1AKE deposition identity and Fixture.closed1AKEManifestation"
  "YueHuLab/LieRMSD"
  "1AKE.pdb"
  "https://github.com/YueHuLab/LieRMSD/blob/main/1AKE.pdb"
  "407ebf46f707592958aaa34df06785d7880ca02a"
  "GitHub blob SHA returned by repository contents API; transport-object identity only"
  true true false false false
  "candidate transport manifestation for executing the AdK PDB->CV script while canonical archive transport is unavailable; must be content-hashed after materialization and later compared with canonical archive bytes"

------------------------------------------------------------------------
-- Promotion policy: a mirror may unblock execution, but every later receipt
-- must continue to carry both transport identity and canonical PDB authority.
------------------------------------------------------------------------

record MirrorExecutionPromotionGate : Set where
  constructor mirror-execution-promotion-gate
  field
    transportObjectObserved : Bool
    exactMaterializedByteSha256Required : Bool
    explicitModelRequired : Bool
    explicitChainRequired : Bool
    explicitAltlocPolicyRequired : Bool
    canonicalArchiveParityRequiredForCanonicalByteClaim : Bool
    mirrorExecutionMayProduceEvaluatorReceipt : Bool
    mirrorExecutionMayProduceScientificAuthority : Bool
open MirrorExecutionPromotionGate public

canonicalMirrorExecutionPromotionGate : MirrorExecutionPromotionGate
canonicalMirrorExecutionPromotionGate =
  mirror-execution-promotion-gate
    true true true true true true true false

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data TransportMirrorCreatesScientificAuthority : Set where
data SamePDBIdCreatesSameBytes : Set where
data GitBlobIdentityCreatesCanonicalArchiveParity : Set where

data ExecutableMirrorReceiptCreatesSourceDefinition : Set where

transportMirrorDoesNotCreateScientificAuthority :
  TransportMirrorCreatesScientificAuthority → ⊥
transportMirrorDoesNotCreateScientificAuthority ()

samePDBIdDoesNotCreateSameBytes : SamePDBIdCreatesSameBytes → ⊥
samePDBIdDoesNotCreateSameBytes ()

gitBlobIdentityDoesNotCreateCanonicalArchiveParity :
  GitBlobIdentityCreatesCanonicalArchiveParity → ⊥
gitBlobIdentityDoesNotCreateCanonicalArchiveParity ()

executableMirrorReceiptDoesNotCreateSourceDefinition :
  ExecutableMirrorReceiptCreatesSourceDefinition → ⊥
executableMirrorReceiptDoesNotCreateSourceDefinition ()

record AdKPDBMirrorTransportBoundary : Set where
  constructor adk-pdb-mirror-transport-boundary
  field
    pdbAuthorityIdentityRetained : Bool
    transportMirrorIdentityRetained : Bool
    gitBlobIdentityRetained : Bool
    mirrorExecutionGateExplicit : Bool
    canonicalArchiveByteEqualityObserved : Bool
    transportMirrorCreatesScientificAuthority : Bool
    samePDBIdCreatesSameBytes : Bool
    gitBlobIdentityCreatesCanonicalArchiveParity : Bool
    executableMirrorReceiptCreatesSourceDefinition : Bool
open AdKPDBMirrorTransportBoundary public

canonicalAdKPDBMirrorTransportBoundary : AdKPDBMirrorTransportBoundary
canonicalAdKPDBMirrorTransportBoundary =
  adk-pdb-mirror-transport-boundary
    true true true true
    false false false false false
