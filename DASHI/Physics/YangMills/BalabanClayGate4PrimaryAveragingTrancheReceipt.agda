module DASHI.Physics.YangMills.BalabanClayGate4PrimaryAveragingTrancheReceipt where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4PrimaryAveragingTrancheLedger as Ledger

record PrimaryAveragingTrancheReceipt : Set where
  constructor primaryAveragingTrancheReceipt
  field
    repositoryHead : String
    primaryDimensionAuditChecked : Bool
    compositionalLocalityChecked : Bool
    primaryPointwiseToRowSumChecked : Bool
    adjointColumnTransportChecked : Bool
    primarySchurBridgeChecked : Bool
    physicalSchurAssemblyChecked : Bool
    constrainedMinimizerProjectionChecked : Bool
    tranchePostulateFree : Bool

open PrimaryAveragingTrancheReceipt public

record AuthoritativePrimaryAveragingEvidence
    (receipt : PrimaryAveragingTrancheReceipt) : Set₁ where
  field
    primaryDimensionAuditTypechecks : Set
    compositionalLocalityTypechecks : Set
    primaryPointwiseToRowSumTypechecks : Set
    adjointColumnTransportTypechecks : Set
    primarySchurBridgeTypechecks : Set
    physicalSchurAssemblyTypechecks : Set
    constrainedMinimizerProjectionTypechecks : Set
    trancheHasNoPostulatesOrUnsolvedMetas : Set

open AuthoritativePrimaryAveragingEvidence public

primaryDimensionAuditTypecheckLevel : ProofLevel
primaryDimensionAuditTypecheckLevel = conditional

compositionalLocalityTypecheckLevel : ProofLevel
compositionalLocalityTypecheckLevel = conditional

primaryPointwiseToRowSumTypecheckLevel : ProofLevel
primaryPointwiseToRowSumTypecheckLevel = conditional

adjointColumnTransportTypecheckLevel : ProofLevel
adjointColumnTransportTypecheckLevel = conditional

primarySchurBridgeTypecheckLevel : ProofLevel
primarySchurBridgeTypecheckLevel = conditional

physicalSchurAssemblyTypecheckLevel : ProofLevel
physicalSchurAssemblyTypecheckLevel = conditional

constrainedMinimizerProjectionTypecheckLevel : ProofLevel
constrainedMinimizerProjectionTypecheckLevel = conditional

primaryAveragingTranchePostulateFreeLevel : ProofLevel
primaryAveragingTranchePostulateFreeLevel = conditional
