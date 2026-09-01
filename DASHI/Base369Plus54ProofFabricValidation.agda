module DASHI.Base369Plus54ProofFabricValidation where

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369Completion54SituatedTriadBridgeExact as Completion
import DASHI.Combinatorics.TextileDependencyGrammarProcessExact as Process
import DASHI.Combinatorics.ProofFabricLocalCompatibilityExact as Local
import DASHI.Combinatorics.ProofFabricCompilerExact as Fabric
import DASHI.Culture.IntellectualReceptionSituatedInformationParetoPreorderExact as Pareto
import Base369 as Base

coarseNinePlusOneRegression :
  Completion.coarseBaseChannels + Completion.coarseCompletionChannels
  ≡ Completion.coarseCarrierChannels
coarseNinePlusOneRegression = Completion.coarseNinePlusOne

coarseBulkRegression :
  Completion.baseBulk + Completion.completionBulk ≡ Completion.coarseBulk
coarseBulkRegression = Completion.coarseBulkDecomposesNinePlusOne

situatedTwoByThreeRegression : 2 * 3 ≡ Completion.situatedSlotCount
situatedTwoByThreeRegression = Completion.twoRowsTimesThreeColumns

comparisonNineRegression : 3 * 3 ≡ Completion.comparisonSheetCount
comparisonNineRegression = Completion.threeTimesThreeIsNine

localCompletion54Regression :
  Completion.situatedSlotCount * Completion.comparisonSheetCount
  ≡ Completion.localCompletionCount
localCompletion54Regression = Completion.sixTimesNineIs54

localResidual53Regression :
  1 + Completion.localResidualCount ≡ Completion.localCompletionCount
localResidual53Regression = Completion.onePlusResidualIs54

base27Times729Regression :
  Completion.base27Count * Completion.ternarySituatedValuationCount
  ≡ Completion.globalFineFibre
base27Times729Regression = Completion.baseTimesAppraisalIsFineFibre

binaryLiftDoesNotProduceMidRegression :
  (level : Pareto.AxisLevel) →
  Completion.axisLevelToTri level ≡ Base.tri-mid → ⊥
binaryLiftDoesNotProduceMidRegression = Completion.binaryProfileNeverIntroducesMid

proofReservedTileRejectedRegression :
  Local.LocallyWellTypedTile Fabric.tile11 → ⊥
proofReservedTileRejectedRegression = Local.reservedTileCannotType

proofCompiledStreamTypedRegression :
  (stream : List DASHI.Algebra.Trit.Trit) →
  Local.LocallyCompatibleFabric (Fabric.compileTritStream stream)
proofCompiledStreamTypedRegression = Local.compiledTritStreamLocallyCompatible

completionBoundaryRegression : Completion.Base369Completion54SituatedTriadBoundary
completionBoundaryRegression = Completion.canonicalBase369Completion54SituatedTriadBoundary

processBoundaryRegression : Process.TextileDependencyGrammarProcessBoundary
processBoundaryRegression = Process.canonicalTextileDependencyGrammarProcessBoundary

proofFabricLocalBoundaryRegression : Local.ProofFabricLocalCompatibilityBoundary
proofFabricLocalBoundaryRegression = Local.canonicalProofFabricLocalCompatibilityBoundary
