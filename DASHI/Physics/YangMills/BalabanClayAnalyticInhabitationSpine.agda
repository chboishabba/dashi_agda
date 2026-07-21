module DASHI.Physics.YangMills.BalabanClayAnalyticInhabitationSpine where

open import Agda.Builtin.Bool using (Bool; false)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanConcreteFiniteBackgroundCutset
import DASHI.Physics.YangMills.BalabanPatchTransferAnalyticReduction
import DASHI.Physics.YangMills.BalabanClayAnalyticConcreteDefinitions
import DASHI.Physics.YangMills.BalabanBulkPropagatorAnalyticInhabitation
import DASHI.Physics.YangMills.BalabanOneStepAllScaleAnalyticInhabitation
import DASHI.Physics.YangMills.BalabanThermodynamicContinuumOSAnalyticInhabitation
import DASHI.Physics.YangMills.BalabanUniformPhysicalMassGapAnalyticInhabitation

------------------------------------------------------------------------
-- One fail-closed status ledger for the complete attached mathematical cutset.
-- The modules above implement every named theorem-facing endpoint and all
-- machine-checkable dependency transport.  Promotion remains closed until the
-- concrete finite-lattice, RG, thermodynamic and continuum analytic records are
-- inhabited without conditional or conjectural leaves.
------------------------------------------------------------------------

bulkFiniteBackgroundAssemblyLevel : ProofLevel
bulkFiniteBackgroundAssemblyLevel = machineChecked

bulkFiniteBackgroundInputLevel : ProofLevel
bulkFiniteBackgroundInputLevel = conditional

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

clayYangMillsSubmissionPromoted : Bool
clayYangMillsSubmissionPromoted = false
