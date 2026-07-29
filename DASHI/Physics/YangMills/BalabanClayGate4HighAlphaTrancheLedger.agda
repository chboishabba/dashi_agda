module DASHI.Physics.YangMills.BalabanClayGate4HighAlphaTrancheLedger where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4FiniteVisitedSetBFSAlgorithmExact as BFS
import DASHI.Physics.YangMills.BalabanClayGate4FiniteVisitedSetBFSParentCorrectnessExact as BFSParent
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicExecutableBFSInstantiationExact as PeriodicBFS
import DASHI.Physics.YangMills.BalabanClayGate4StrongBFSParentCertificateExact as StrongBFS
import DASHI.Physics.YangMills.BalabanClayGate4BFSAdjacentLayerShortestPathExact as BFSShortest
import DASHI.Physics.YangMills.BalabanClayGate4FiniteCoercivityInverseNormExact as InverseNorm
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
periodicPolymerInducedGraphLevel = PeriodicBFS.periodicPolymerInducedGraphLevel
periodicEqualityBooleanReflectionLevel =
  PeriodicBFS.periodicEqualityBooleanReflectionLevel
periodicAdjacencyBooleanReflectionLevel =
  PeriodicBFS.periodicAdjacencyBooleanReflectionLevel
periodicFuelBoundedBFSExecutionLevel =
  PeriodicBFS.periodicFuelBoundedBFSExecutionLevel
periodicPolymerFuelBoundedBFSExecutionLevel =
  PeriodicBFS.periodicPolymerFuelBoundedBFSExecutionLevel
periodicLocalParentCorrectnessLevel =
  PeriodicBFS.periodicLocalParentCorrectnessLevel
strongBFSParentCertificateLevel = StrongBFS.strongBFSParentCertificateLevel
parentChainDistanceLevel = StrongBFS.parentChainDistanceLevel
parentAcyclicityFromDistanceDescentLevel =
  StrongBFS.parentAcyclicityFromDistanceDescentLevel
parentConnectivityFromDistanceDescentLevel =
  StrongBFS.parentConnectivityFromDistanceDescentLevel
rootPathAtAssignedDistanceLevel = StrongBFS.rootPathAtAssignedDistanceLevel
adjacentLayerUpperBoundReductionLevel =
  BFSShortest.adjacentLayerUpperBoundReductionLevel
shortestPathFromAdjacentLayerInvariantLevel =
  BFSShortest.shortestPathFromAdjacentLayerInvariantLevel

finiteSpectralInverseNormReductionLevel =
  InverseNorm.finiteSpectralInverseNormReductionLevel
coercivityReciprocalInverseBoundLevel =
  InverseNorm.coercivityReciprocalInverseBoundLevel
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

-- The historical Set-valued BFS labels remain for compatibility. The preferred
-- proof boundary is now the strong distance certificate below.
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
physicalPeriodicDistanceStepInputsLevel =
  StrongBFS.physicalPeriodicDistanceStepInputsLevel
physicalPeriodicDistanceZeroUniquenessInputsLevel =
  StrongBFS.physicalPeriodicDistanceZeroUniquenessInputsLevel
physicalPeriodicAdjacentLayerUpperBoundInputsLevel =
  BFSShortest.physicalPeriodicAdjacentLayerUpperBoundInputsLevel

physicalCoercivityToSpectrumLowerBoundInputsLevel =
  InverseNorm.physicalCoercivityToSpectrumLowerBoundInputsLevel
physicalInverseHessianSpectralNormMeaningInputsLevel =
  InverseNorm.physicalInverseHessianSpectralNormMeaningInputsLevel
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
