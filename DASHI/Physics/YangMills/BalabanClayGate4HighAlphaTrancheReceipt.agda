module DASHI.Physics.YangMills.BalabanClayGate4HighAlphaTrancheReceipt where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4HighAlphaTrancheLedger as Ledger

record HighAlphaTrancheReceipt : Set where
  constructor highAlphaTrancheReceipt
  field
    repositoryHead : String
    executableVisitedSetBFSChecked : Bool
    bfsParentCorrectnessChecked : Bool
    periodicExecutableBFSChecked : Bool
    strongBFSParentCertificateChecked : Bool
    adjacentLayerShortestPathReductionChecked : Bool
    finiteCoercivityInverseNormChecked : Bool
    ipsenRehmanDeterminantBridgeChecked : Bool
    ipsenRehmanCompensatedTAdapterChecked : Bool
    finiteKernelSchurBridgeChecked : Bool
    exactTwoWeightKPBridgeChecked : Bool
    physicalTerminalKPAdapterChecked : Bool
    anisotropyPolymerSummationChecked : Bool
    correctedProvenanceChecked : Bool
    tranchePostulateFree : Bool

open HighAlphaTrancheReceipt public

record AuthoritativeHighAlphaEvidence
    (receipt : HighAlphaTrancheReceipt) : Set₁ where
  field
    executableVisitedSetBFSTypechecks : Set
    bfsParentCorrectnessTypechecks : Set
    periodicExecutableBFSTypechecks : Set
    strongBFSParentCertificateTypechecks : Set
    adjacentLayerShortestPathReductionTypechecks : Set
    finiteCoercivityInverseNormTypechecks : Set
    ipsenRehmanDeterminantBridgeTypechecks : Set
    ipsenRehmanCompensatedTAdapterTypechecks : Set
    finiteKernelSchurBridgeTypechecks : Set
    exactTwoWeightKPBridgeTypechecks : Set
    physicalTerminalKPAdapterTypechecks : Set
    anisotropyPolymerSummationTypechecks : Set
    correctedProvenanceTypechecks : Set
    trancheHasNoPostulatesOrUnsolvedMetas : Set

open AuthoritativeHighAlphaEvidence public

executableVisitedSetBFSTypecheckLevel : ProofLevel
executableVisitedSetBFSTypecheckLevel = conditional

bfsParentCorrectnessTypecheckLevel : ProofLevel
bfsParentCorrectnessTypecheckLevel = conditional

periodicExecutableBFSTypecheckLevel : ProofLevel
periodicExecutableBFSTypecheckLevel = conditional

strongBFSParentCertificateTypecheckLevel : ProofLevel
strongBFSParentCertificateTypecheckLevel = conditional

adjacentLayerShortestPathReductionTypecheckLevel : ProofLevel
adjacentLayerShortestPathReductionTypecheckLevel = conditional

finiteCoercivityInverseNormTypecheckLevel : ProofLevel
finiteCoercivityInverseNormTypecheckLevel = conditional

ipsenRehmanDeterminantBridgeTypecheckLevel : ProofLevel
ipsenRehmanDeterminantBridgeTypecheckLevel = conditional

ipsenRehmanCompensatedTAdapterTypecheckLevel : ProofLevel
ipsenRehmanCompensatedTAdapterTypecheckLevel = conditional

finiteKernelSchurBridgeTypecheckLevel : ProofLevel
finiteKernelSchurBridgeTypecheckLevel = conditional

exactTwoWeightKPBridgeTypecheckLevel : ProofLevel
exactTwoWeightKPBridgeTypecheckLevel = conditional

physicalTerminalKPAdapterTypecheckLevel : ProofLevel
physicalTerminalKPAdapterTypecheckLevel = conditional

anisotropyPolymerSummationTypecheckLevel : ProofLevel
anisotropyPolymerSummationTypecheckLevel = conditional

correctedProvenanceTypecheckLevel : ProofLevel
correctedProvenanceTypecheckLevel = conditional

highAlphaTranchePostulateFreeLevel : ProofLevel
highAlphaTranchePostulateFreeLevel = conditional
