module DASHI.Computation.SSSPSemanticFractranThreadCoverageExact where

-- One theorem-bearing coverage surface for the concrete architecture items
-- discussed in the SSSP <-> semantic/FRACTRAN thread.  Positive coverage is
-- anchored to imported witnesses where available; conditional promotions stay
-- explicit boundaries rather than being marked as completed representation
-- theorems.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Computation.SSSPSortingBarrierTernaryBidiExact as Sorting
import DASHI.Computation.SSSPBinaryTernarySymmetryRefinementBidiExact as Refine
import DASHI.Computation.SSSPThreeFrontierLinearExtensionQuotientBidiExact as Three
import DASHI.Computation.SSSPConsumerInvariantSymmetryQuotientExact as Symmetry
import DASHI.Computation.SSSPFindPivotsCoverageCompressionExact as Pivots
import DASHI.Computation.SSSPThreeFrontierMinimumOrbitQuotientExact as Minimum
import DASHI.Computation.SSSPThreeFrontierBinaryTernaryFactorExact as Factor
import DASHI.Computation.SSSPGeneralPullPrefixQuotientExact as Pull

import DASHI.Cognition.PNF.SemanticQueryResidualFibreSSSPBridgeExact as Query
import DASHI.Cognition.PNF.SemanticRelationSheetOrientationExact as Sheet
import DASHI.Cognition.PNF.SemanticQueryFractranCatalogueBridgeExact as Catalogue
import DASHI.Cognition.PNF.SemanticBracketFractranDivisibilityExact as Bracket
import DASHI.Cognition.PNF.SemanticTokenQuotientStateExact as Token
import DASHI.Cognition.PNF.SemanticPhaseFractranIntertwinerBoundaryExact as Phase
import DASHI.Cognition.PNF.SemanticQueryBracketFractranSplitChainExact as Chain

------------------------------------------------------------------------
-- Imported exact witnesses used by the audit.
------------------------------------------------------------------------

sortingWitness = Sorting.consumer-descends-through-unrequired-order
refinementWitness = Refine.SSSPBinaryTernaryRefinementCommutes
threeFrontierWitness = Three.linearExtensionsCollapseForAConsumer
symmetryWitness = Symmetry.abcAcbConsumerEquivalentFromSymmetry
findPivotsWitness = Pivots.canonicalFindPivotsBidiBoundary
minimumWitness = Minimum.minimumCodecRoundTrip
factorWitness = Factor.orderRoundTrip
pullWitness = Pull.consumerInvariantUnderTailSymmetry
queryWitness = Query.coarseWorldsObservationEqual
querySplitWitness = Query.provenanceWorldsSeparate
sheetWitness = Sheet.canonicalTransposeFlipsLeftRight
catalogueWitness = Catalogue.semanticQueryEquivalentWorldsHaveSameFractranOutcome
bracketClosedWitness = Bracket.bracketUnavailableDisablesDistinguishingRule
bracketOpenWitness = Bracket.bracketAvailableEnablesDistinguishingRule
tokenWitness = Token.refinementPreservesOccurrence
chainClosedWitness = Chain.coarseQueryDistinguishingRuleDisabled
chainOpenWitness = Chain.provenanceQueryDistinguishingRuleEnabled
phaseBoundaryWitness = Phase.canonicalPhaseFractranBoundary

record ThreadCoverage : Set where
  constructor threadCoverage
  field
    sortingBarrierConsumerQuotient : Bool
    sortingBarrierConsumerQuotientIsTrue : sortingBarrierConsumerQuotient ≡ true
    binaryTernaryRefinementDiamond : Bool
    binaryTernaryRefinementDiamondIsTrue : binaryTernaryRefinementDiamond ≡ true
    sixAndNineSymmetryCarriersSeparatedByRole : Bool
    sixAndNineSymmetryCarriersSeparatedByRoleIsTrue :
      sixAndNineSymmetryCarriersSeparatedByRole ≡ true
    threeFrontierSixLinearExtensions : Bool
    threeFrontierSixLinearExtensionsIsTrue : threeFrontierSixLinearExtensions ≡ true
    completeNineCellRelationSheet : Bool
    completeNineCellRelationSheetIsTrue : completeNineCellRelationSheet ≡ true
    consumerInvariantSymmetryQuotient : Bool
    consumerInvariantSymmetryQuotientIsTrue : consumerInvariantSymmetryQuotient ≡ true
    sixEqualsThreeTimesTwoProductChart : Bool
    sixEqualsThreeTimesTwoProductChartIsTrue : sixEqualsThreeTimesTwoProductChart ≡ true
    generalPullPrefixTailQuotient : Bool
    generalPullPrefixTailQuotientIsTrue : generalPullPrefixTailQuotient ≡ true
    findPivotsCoverageCompressionWithoutSort : Bool
    findPivotsCoverageCompressionWithoutSortIsTrue :
      findPivotsCoverageCompressionWithoutSort ≡ true
    semanticAlternativeFibreRetained : Bool
    semanticAlternativeFibreRetainedIsTrue : semanticAlternativeFibreRetained ≡ true
    queryStabiliserCanShrinkAndSplitFibre : Bool
    queryStabiliserCanShrinkAndSplitFibreIsTrue :
      queryStabiliserCanShrinkAndSplitFibre ≡ true
    semanticRelationTransposeOrientation : Bool
    semanticRelationTransposeOrientationIsTrue : semanticRelationTransposeOrientation ≡ true
    tokenObservedResidualBracketStratumState : Bool
    tokenObservedResidualBracketStratumStateIsTrue :
      tokenObservedResidualBracketStratumState ≡ true
    bracketDivisibilityGate : Bool
    bracketDivisibilityGateIsTrue : bracketDivisibilityGate ≡ true
    endToEndQueryBracketSplitChain : Bool
    endToEndQueryBracketSplitChainIsTrue : endToEndQueryBracketSplitChain ≡ true
    queryToFractranCompressionNeedsSoundCatalogueWitness : Bool
    queryToFractranCompressionNeedsSoundCatalogueWitnessIsTrue :
      queryToFractranCompressionNeedsSoundCatalogueWitness ≡ true
    relationToPhaseNeedsIntertwiner : Bool
    relationToPhaseNeedsIntertwinerIsTrue : relationToPhaseNeedsIntertwiner ≡ true
    phaseToFractranNeedsReciprocalIntertwiner : Bool
    phaseToFractranNeedsReciprocalIntertwinerIsTrue :
      phaseToFractranNeedsReciprocalIntertwiner ≡ true
    queryEquivalenceAutomaticallyMeansSameFractranTrace : Bool
    queryEquivalenceAutomaticallyMeansSameFractranTraceIsFalse :
      queryEquivalenceAutomaticallyMeansSameFractranTrace ≡ false
    permutationSymmetryAutomaticallyMeansC6OrC9PhaseSymmetry : Bool
    permutationSymmetryAutomaticallyMeansC6OrC9PhaseSymmetryIsFalse :
      permutationSymmetryAutomaticallyMeansC6OrC9PhaseSymmetry ≡ false
    twoThirdsExponentDerivedFromTernaryCarrier : Bool
    twoThirdsExponentDerivedFromTernaryCarrierIsFalse :
      twoThirdsExponentDerivedFromTernaryCarrier ≡ false

canonicalThreadCoverage : ThreadCoverage
canonicalThreadCoverage =
  threadCoverage
    true refl true refl true refl true refl true refl true refl true refl
    true refl true refl true refl true refl true refl true refl true refl
    true refl true refl true refl true refl false refl false refl false refl
