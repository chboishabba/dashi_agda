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
    primaryBibliographyChecked : Bool
    compositionalLocalityChecked : Bool
    primaryPointwiseToRowSumChecked : Bool
    adjointColumnTransportChecked : Bool
    primarySchurBridgeChecked : Bool
    physicalSchurAssemblyChecked : Bool
    weightedSchurChecked : Bool
    primaryWeightedSchurChecked : Bool
    periodicSupportEnumerationChecked : Bool
    periodicUniformBoundsChecked : Bool
    periodicPrimaryKernelInstantiationChecked : Bool
    constrainedMinimizerProjectionChecked : Bool
    constrainedHessianRestrictionChecked : Bool
    primaryBetaFiniteDifferenceChecked : Bool
    tranchePostulateFree : Bool

open PrimaryAveragingTrancheReceipt public

record AuthoritativePrimaryAveragingEvidence
    (receipt : PrimaryAveragingTrancheReceipt) : Set₁ where
  field
    primaryDimensionAuditTypechecks : Set
    primaryBibliographyTypechecks : Set
    compositionalLocalityTypechecks : Set
    primaryPointwiseToRowSumTypechecks : Set
    adjointColumnTransportTypechecks : Set
    primarySchurBridgeTypechecks : Set
    physicalSchurAssemblyTypechecks : Set
    weightedSchurTypechecks : Set
    primaryWeightedSchurTypechecks : Set
    periodicSupportEnumerationTypechecks : Set
    periodicUniformBoundsTypechecks : Set
    periodicPrimaryKernelInstantiationTypechecks : Set
    constrainedMinimizerProjectionTypechecks : Set
    constrainedHessianRestrictionTypechecks : Set
    primaryBetaFiniteDifferenceTypechecks : Set
    trancheHasNoPostulatesOrUnsolvedMetas : Set

open AuthoritativePrimaryAveragingEvidence public

primaryDimensionAuditTypecheckLevel : ProofLevel
primaryDimensionAuditTypecheckLevel = conditional

primaryBibliographyTypecheckLevel : ProofLevel
primaryBibliographyTypecheckLevel = conditional

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

weightedSchurTypecheckLevel : ProofLevel
weightedSchurTypecheckLevel = conditional

primaryWeightedSchurTypecheckLevel : ProofLevel
primaryWeightedSchurTypecheckLevel = conditional

periodicSupportEnumerationTypecheckLevel : ProofLevel
periodicSupportEnumerationTypecheckLevel = conditional

periodicUniformBoundsTypecheckLevel : ProofLevel
periodicUniformBoundsTypecheckLevel = conditional

periodicPrimaryKernelInstantiationTypecheckLevel : ProofLevel
periodicPrimaryKernelInstantiationTypecheckLevel = conditional

constrainedMinimizerProjectionTypecheckLevel : ProofLevel
constrainedMinimizerProjectionTypecheckLevel = conditional

constrainedHessianRestrictionTypecheckLevel : ProofLevel
constrainedHessianRestrictionTypecheckLevel = conditional

primaryBetaFiniteDifferenceTypecheckLevel : ProofLevel
primaryBetaFiniteDifferenceTypecheckLevel = conditional

primaryAveragingTranchePostulateFreeLevel : ProofLevel
primaryAveragingTranchePostulateFreeLevel = conditional
