module DASHI.Physics.YangMills.BalabanClayGate4HighAlphaTrancheLedger where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4FiniteVisitedSetBFSAlgorithmExact as BFS
import DASHI.Physics.YangMills.BalabanClayGate4FiniteVisitedSetBFSParentCorrectnessExact as BFSParent
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicExecutableBFSInstantiationExact as PeriodicBFS
import DASHI.Physics.YangMills.BalabanClayGate4IpsenRehmanDeterminantLossExact as Determinant
import DASHI.Physics.YangMills.BalabanClayGate4IpsenRehmanCompensatedTAdapterExact as DeterminantT
import DASHI.Physics.YangMills.BalabanClayGate4FiniteKernelSchurBlockAdjointExact as Schur
import DASHI.Physics.YangMills.BalabanClayT5KoteckyPreissTwoWeightPrimaryExact as KP
import DASHI.Physics.YangMills.BalabanClayT5PhysicalTwoWeightKoteckyPreissExact as PhysicalKP
import DASHI.Physics.YangMills.BalabanClayT5AnisotropyPolymerSummationExact as Anisotropy
import DASHI.Physics.YangMills.BalabanClayGate4AnisotropyBlockAndCriterionProvenanceExact as Provenance

------------------------------------------------------------------------
-- Concise ledger for the highest-alpha tranche described in the attached proof
-- plan. The exact finite reductions are separated from their remaining
-- physical Yang--Mills identifications and uniform analytic estimates.
------------------------------------------------------------------------

executableVisitedSetBFSDefinitionLevel =
  BFS.executableVisitedSetBFSDefinitionLevel
fuelBoundedTerminationByConstructionLevel =
  BFS.fuelBoundedTerminationByConstructionLevel
canonicalPreviousLayerParentDefinitionLevel =
  BFS.canonicalPreviousLayerParentDefinitionLevel
firstAdjacentParentSoundLevel = BFSParent.firstAdjacentParentSoundLevel
firstAdjacentParentCanonicalOrderLevel =
  BFSParent.firstAdjacentParentCanonicalOrderLevel
discoveredParentEdgesSoundLevel = BFSParent.discoveredParentEdgesSoundLevel
periodicExecutableGraphLevel = PeriodicBFS.periodicExecutableGraphLevel
periodicEqualityBooleanReflectionLevel =
  PeriodicBFS.periodicEqualityBooleanReflectionLevel
periodicAdjacencyBooleanReflectionLevel =
  PeriodicBFS.periodicAdjacencyBooleanReflectionLevel
periodicFuelBoundedBFSExecutionLevel =
  PeriodicBFS.periodicFuelBoundedBFSExecutionLevel
periodicLocalParentCorrectnessLevel =
  PeriodicBFS.periodicLocalParentCorrectnessLevel

ipsenRehmanStatementProvenanceLevel =
  Determinant.ipsenRehmanStatementProvenanceLevel
finiteDeterminantExponentialLossAssemblyLevel =
  Determinant.finiteDeterminantExponentialLossAssemblyLevel
physicalDeterminantMultiplierAssemblyLevel =
  Determinant.physicalDeterminantMultiplierAssemblyLevel
ipsenRehmanCompensatedTAdapterLevel =
  DeterminantT.ipsenRehmanCompensatedTAdapterLevel

finiteKernelSchurReductionLevel = Schur.finiteKernelSchurReductionLevel
oneEighthKernelBudgetAssemblyLevel = Schur.oneEighthKernelBudgetAssemblyLevel
physicalBlockAdjointRelativeContractionAssemblyLevel =
  Schur.physicalBlockAdjointRelativeContractionAssemblyLevel

koteckyPreissPrimaryStatementLevel = KP.koteckyPreissPrimaryStatementLevel
rootedTerminalToTwoWeightKPAssemblyLevel =
  KP.rootedTerminalToTwoWeightKPAssemblyLevel
physicalTerminalTwoWeightKPAssemblyLevel =
  PhysicalKP.physicalTerminalTwoWeightKPAssemblyLevel
physicalTerminalPublishedKPConclusionLevel =
  PhysicalKP.physicalTerminalPublishedKPConclusionLevel

finiteAnisotropySummationLevel = Anisotropy.finiteAnisotropySummationLevel
totalAnisotropyA2EnvelopeAssemblyLevel =
  Anisotropy.totalAnisotropyA2EnvelopeAssemblyLevel

anisotropyBenchmarkNormalizationLevel =
  Provenance.anisotropyBenchmarkNormalizationLevel
blockRGMethodProvenanceLevel = Provenance.blockRGMethodProvenanceLevel
primaryKPTwoWeightProvenanceLevel =
  Provenance.primaryKPTwoWeightProvenanceLevel
balabanEquation175SingleLocatorLevel =
  Provenance.balabanEquation175SingleLocatorLevel

------------------------------------------------------------------------
-- Remaining physical and correctness inhabitants.
------------------------------------------------------------------------

bfsDistanceLayerInvariantInputsLevel =
  BFSParent.bfsDistanceLayerInvariantInputsLevel
bfsSpanningAndAcyclicityInputsLevel =
  BFSParent.bfsSpanningAndAcyclicityInputsLevel
periodicBFSShortestPathInvariantInputsLevel =
  PeriodicBFS.periodicBFSShortestPathInvariantInputsLevel
periodicBFSParentTreeCorrectnessInputsLevel =
  PeriodicBFS.periodicBFSParentTreeCorrectnessInputsLevel
periodicBFSImplementationAssemblyInputsLevel =
  BFS.periodicBFSImplementationAssemblyInputsLevel

physicalReferenceHessianInvertibilityInputsLevel =
  Determinant.physicalReferenceHessianInvertibilityInputsLevel
physicalHessianPerturbationNormInputsLevel =
  Determinant.physicalHessianPerturbationNormInputsLevel
physicalIpsenRehmanNormIdentificationInputsLevel =
  Determinant.physicalIpsenRehmanNormIdentificationInputsLevel
physicalFiniteHessianToTDeterminantMeaningInputsLevel =
  DeterminantT.physicalFiniteHessianToTDeterminantMeaningInputsLevel
physicalDeterminantRationalOrderMeaningInputsLevel =
  DeterminantT.physicalDeterminantRationalOrderMeaningInputsLevel

physicalBlockAdjointKernelIdentificationInputsLevel =
  Schur.physicalBlockAdjointKernelIdentificationInputsLevel
physicalBlockAdjointRowColumnSumInputsLevel =
  Schur.physicalBlockAdjointRowColumnSumInputsLevel

physicalTerminalIncompatibilitySumMeaningInputsLevel =
  KP.physicalTerminalIncompatibilitySumMeaningInputsLevel
physicalTerminalAAndDWeightMeaningInputsLevel =
  KP.physicalTerminalAAndDWeightMeaningInputsLevel
physicalFernandezProcacciDirectCriterionInputsLevel =
  KP.physicalFernandezProcacciDirectCriterionInputsLevel
physicalTerminalTwoWeightMeaningInputsLevel =
  PhysicalKP.physicalTerminalTwoWeightMeaningInputsLevel
physicalTerminalFernandezProcacciFallbackInputsLevel =
  PhysicalKP.physicalTerminalFernandezProcacciFallbackInputsLevel

physicalPerPolymerAnisotropyA2InputsLevel =
  Anisotropy.physicalPerPolymerAnisotropyA2InputsLevel
physicalAnisotropyMajorantSummabilityInputsLevel =
  Anisotropy.physicalAnisotropyMajorantSummabilityInputsLevel
physicalA2EnvelopeContinuumMeaningInputsLevel =
  Anisotropy.physicalA2EnvelopeContinuumMeaningInputsLevel
