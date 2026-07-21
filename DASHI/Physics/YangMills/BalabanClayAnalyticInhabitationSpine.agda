module DASHI.Physics.YangMills.BalabanClayAnalyticInhabitationSpine where

open import Agda.Builtin.Bool using (Bool; false)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanConcreteFiniteBackgroundCutset
import DASHI.Physics.YangMills.BalabanPatchTransferAnalyticReduction
import DASHI.Physics.YangMills.BalabanExactPatchTransferCalculus
import DASHI.Physics.YangMills.BalabanClayAnalyticConcreteDefinitions
import DASHI.Physics.YangMills.BalabanBulkPropagatorAnalyticInhabitation
import DASHI.Physics.YangMills.BalabanPublishedAnalyticAuthorities
import DASHI.Physics.YangMills.BalabanPublishedAuthorityAdapters
import DASHI.Physics.YangMills.BalabanExactPublishedCarrierMatching
import DASHI.Physics.YangMills.BalabanOneStepAllScaleAnalyticInhabitation
import DASHI.Physics.YangMills.BalabanThermodynamicContinuumOSAnalyticInhabitation
import DASHI.Physics.YangMills.BalabanUniformPhysicalMassGapAnalyticInhabitation
import DASHI.Physics.YangMills.BalabanUnconditionalSolutionCertificate

------------------------------------------------------------------------
-- One fail-closed status ledger for the complete attached mathematical cutset.
------------------------------------------------------------------------

bulkFiniteBackgroundAssemblyLevel : ProofLevel
bulkFiniteBackgroundAssemblyLevel = machineChecked

bulkFiniteBackgroundInputLevel : ProofLevel
bulkFiniteBackgroundInputLevel = conditional

publishedPropagatorAndVariationalTheoremsLevel : ProofLevel
publishedPropagatorAndVariationalTheoremsLevel = standardImported

publishedCarrierAdapterLevel : ProofLevel
publishedCarrierAdapterLevel = machineChecked

exactPublishedCarrierAdapterLevel : ProofLevel
exactPublishedCarrierAdapterLevel = machineChecked

publishedCarrierMatchingLevel : ProofLevel
publishedCarrierMatchingLevel = conditional

patchTransferAssemblyLevel : ProofLevel
patchTransferAssemblyLevel = machineChecked

patchTransferInputLevel : ProofLevel
patchTransferInputLevel = conditional

oneStepAndAllScaleAssemblyLevel : ProofLevel
oneStepAndAllScaleAssemblyLevel = machineChecked

oneStepAndAllScaleInputLevel : ProofLevel
oneStepAndAllScaleInputLevel = conditional

thermodynamicAssemblyLevel : ProofLevel
thermodynamicAssemblyLevel = machineChecked

thermodynamicInputLevel : ProofLevel
thermodynamicInputLevel = conditional

continuumOSAssemblyLevel : ProofLevel
continuumOSAssemblyLevel = machineChecked

continuumOSInputLevel : ProofLevel
continuumOSInputLevel = conjectural

physicalMassGapAssemblyLevel : ProofLevel
physicalMassGapAssemblyLevel = machineChecked

physicalMassGapInputLevel : ProofLevel
physicalMassGapInputLevel = conjectural

unconditionalSolutionGateLevel : ProofLevel
unconditionalSolutionGateLevel = machineChecked

unconditionalSolutionInhabitationLevel : ProofLevel
unconditionalSolutionInhabitationLevel = conjectural

-- The nullary repository status remains false.  The separate proof-relevant
-- `clayYangMillsSubmissionPromotion` function can return true only after an
-- `UnconditionalYangMillsSolution` value has actually been constructed.
clayYangMillsSubmissionPromoted : Bool
clayYangMillsSubmissionPromoted = false
