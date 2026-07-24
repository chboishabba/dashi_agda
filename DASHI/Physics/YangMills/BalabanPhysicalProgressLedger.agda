module DASHI.Physics.YangMills.BalabanPhysicalProgressLedger where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanFiniteEnumerationDistinctExact
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
import DASHI.Physics.YangMills.BalabanPhysicalBlockEnumerationDistinctExact
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
import DASHI.Physics.YangMills.BalabanPath4PhysicalFibreMatchExact
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact
import DASHI.Physics.YangMills.BalabanFourAxisMartingaleExact
import DASHI.Physics.YangMills.BalabanCommutingProjectionMartingaleExact
import DASHI.Physics.YangMills.BalabanPhysicalHaloOriginExact
import DASHI.Physics.YangMills.BalabanSU2AdjointRadiusSquared
import DASHI.Physics.YangMills.BalabanNonlinearDifferenceIdentitiesExact
import DASHI.Physics.YangMills.BalabanQuadraticOperatorPerturbationExact
import DASHI.Physics.YangMills.BalabanMultilinearLipschitzCalculus
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact
import DASHI.Physics.YangMills.BalabanConcreteRootedTracePolymer
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact
import DASHI.Physics.YangMills.BalabanRunningCouplingIterationExact

------------------------------------------------------------------------
-- Exact progress and the remaining producer boundary are intentionally listed
-- side by side.  A downstream aggregate cannot mistake a finite reduction for
-- the missing physical Wilson, polymer-activity or beta-remainder theorem.
------------------------------------------------------------------------

literalPhysicalBlockCarrierLevel : ProofLevel
literalPhysicalBlockCarrierLevel = machineChecked

literalPhysicalBlockDistinctnessLevel : ProofLevel
literalPhysicalBlockDistinctnessLevel = machineChecked

literalPhysicalFibreMeanZeroEnergyLevel : ProofLevel
literalPhysicalFibreMeanZeroEnergyLevel = machineChecked

path4PhysicalFibreCertificateLevel : ProofLevel
path4PhysicalFibreCertificateLevel = machineChecked

path4AxisAverageAlgebraLevel : ProofLevel
path4AxisAverageAlgebraLevel = computed

commutingProjectionOrthogonalityLevel : ProofLevel
commutingProjectionOrthogonalityLevel = machineChecked

physicalAxisAverageSelfAdjointnessLevel : ProofLevel
physicalAxisAverageSelfAdjointnessLevel = conditional

physicalFourDimensionalTensorizationLevel : ProofLevel
physicalFourDimensionalTensorizationLevel = conditional

literalPhysicalHaloOriginLevel : ProofLevel
literalPhysicalHaloOriginLevel = machineChecked

physicalOriginWilsonContainmentMatchLevel : ProofLevel
physicalOriginWilsonContainmentMatchLevel = conditional

su2SquaredRadiusTransportLevel : ProofLevel
su2SquaredRadiusTransportLevel = machineChecked

su2ExponentialChartRadiusInputLevel : ProofLevel
su2ExponentialChartRadiusInputLevel = conditional

quadraticOperatorExpansionLevel : ProofLevel
quadraticOperatorExpansionLevel = machineChecked

multilinearLipschitzReductionLevel : ProofLevel
multilinearLipschitzReductionLevel = machineChecked

literalFiveWilsonOperatorBoundsLevel : ProofLevel
literalFiveWilsonOperatorBoundsLevel = conditional

literalSevenNonlinearMapBoundsLevel : ProofLevel
literalSevenNonlinearMapBoundsLevel = conditional

rootedTracePolymerEntropyLevel : ProofLevel
rootedTracePolymerEntropyLevel = machineChecked

finiteTraceKoteckyPreissLevel : ProofLevel
finiteTraceKoteckyPreissLevel = machineChecked

physicalPolymerTraceInjectionLevel : ProofLevel
physicalPolymerTraceInjectionLevel = conditional

physicalLargeFieldActivitySuppressionLevel : ProofLevel
physicalLargeFieldActivitySuppressionLevel = conditional

runningCouplingIterationLevel : ProofLevel
runningCouplingIterationLevel = machineChecked

terminalOffsetScaleFactorizationLevel : ProofLevel
terminalOffsetScaleFactorizationLevel = machineChecked

physicalBetaRemainderLevel : ProofLevel
physicalBetaRemainderLevel = conditional

physicalTerminalOffsetBoundLevel : ProofLevel
physicalTerminalOffsetBoundLevel = conjectural

dimensionalTransmutationInvariantLevel : ProofLevel
dimensionalTransmutationInvariantLevel = conjectural
