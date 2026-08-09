module DASHI.Reasoning.RelationalBranchGeometryRegression where

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_; -[1+_]) renaming (_+_ to _+ℤ_)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Physics.ShiftDiscreteWaveStep as Wave
import DASHI.Physics.ShiftUnitaryLikeConstraint as Norm
import DASHI.Reasoning.RelationalBranchInterference as Interference
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Cobordism
import DASHI.Reasoning.RelationalTernaryPhaseGeometry as Ternary
import DASHI.Reasoning.RelationalGeometricProcessIntegration as Integration
import DASHI.Reasoning.RelationalBranchGeometrySourceAtlas as Sources

------------------------------------------------------------------------
-- Source and authority regressions.
------------------------------------------------------------------------

branchGeometrySourceCountRegression :
  Sources.canonicalBranchGeometrySourceCount ≡ 3
branchGeometrySourceCountRegression = refl

branchGeometryAtlasCreatesNoAuthority :
  Attr.atlasCreatesAuthority Sources.canonicalBranchGeometrySourceAtlas ≡ false
branchGeometryAtlasCreatesNoAuthority =
  Sources.canonicalBranchGeometryAtlasDoesNotCreateAuthority

finitePantsIsNotPromotedToSmoothCobordism :
  Cobordism.smoothCobordismClaimed
    Cobordism.canonicalBranchCobordismAuthorityBoundary
  ≡ false
finitePantsIsNotPromotedToSmoothCobordism = refl

jScaleLabelsAreNotModularJ :
  Cobordism.modularJInvariantClaimed
    Cobordism.canonicalBranchCobordismAuthorityBoundary
  ≡ false
jScaleLabelsAreNotModularJ = refl

------------------------------------------------------------------------
-- Exact pants/cobordism composition regressions.
------------------------------------------------------------------------

composedPantsHasThreeFineLegs :
  Cobordism.outputCount Cobordism.composedOneToThree ≡ 3
composedPantsHasThreeFineLegs = refl

composedPantsConservesCapacity :
  Cobordism.CapacityConservative Cobordism.composedOneToThree
composedPantsConservesCapacity =
  Cobordism.composedCapacityConservative

composedPantsRecombinesExactly :
  Cobordism.WaveConservative Cobordism.composedOneToThree
composedPantsRecombinesExactly =
  Cobordism.composedWaveConservative

composedPantsResidualIsZero :
  Cobordism.splitRecombineResidual Cobordism.composedOneToThree
  ≡ Wave.mkDiscreteWave (+ 0) (+ 0)
composedPantsResidualIsZero = refl

phaseTransportLeavesExactMemoryResidual :
  Cobordism.splitRecombineResidual Cobordism.phaseChangedJunction
  ≡ Wave.mkDiscreteWave (-[1+ 0 ]) (+ 1)
phaseTransportLeavesExactMemoryResidual = refl

------------------------------------------------------------------------
-- Exact symmetric ternary and ordered ternary regressions.
------------------------------------------------------------------------

symmetricTernaryRootsCancel :
  Ternary.sumE
    (Ternary.rootOne
      ∷ Ternary.rootOmega
      ∷ Ternary.rootOmegaSquared
      ∷ [])
  ≡ Ternary.zeroE
symmetricTernaryRootsCancel = refl

symmetricTernaryIntensityIsZero :
  Ternary.normE
    (Ternary.sumE
      (Ternary.rootOne
        ∷ Ternary.rootOmega
        ∷ Ternary.rootOmegaSquared
        ∷ []))
  ≡ + 0
symmetricTernaryIntensityIsZero = refl

symmetricTernaryPairwiseLedgerCancelsDiagonal :
  (Ternary.normE Ternary.rootOne
    +ℤ Ternary.normE Ternary.rootOmega
    +ℤ Ternary.normE Ternary.rootOmegaSquared)
  +ℤ
  (Ternary.pairInterferenceE Ternary.rootOne Ternary.rootOmega
    +ℤ Ternary.pairInterferenceE
      Ternary.rootOne Ternary.rootOmegaSquared
    +ℤ Ternary.pairInterferenceE
      Ternary.rootOmega Ternary.rootOmegaSquared)
  ≡ + 0
symmetricTernaryPairwiseLedgerCancelsDiagonal = refl

orderedAlignmentTripleDoesNotSymmetricallyCancel :
  Interference.coherentIntensity
    (Ternary.orderedWave Ternary.alignedDirection
      ∷ Ternary.orderedWave Ternary.openOrthogonalDirection
      ∷ Ternary.orderedWave Ternary.opposedDirection
      ∷ [])
  ≡ + 1
orderedAlignmentTripleDoesNotSymmetricallyCancel = refl

symmetricAndOrderedTernaryAreNotInterchangeable :
  Ternary.symmetricAndOrderedGeometriesAreInterchangeable
    Ternary.canonicalTernaryPhaseAuthorityBoundary
  ≡ false
symmetricAndOrderedTernaryAreNotInterchangeable = refl

------------------------------------------------------------------------
-- Attractor-projected coherence regressions.
------------------------------------------------------------------------

twoAlignedBranchesHaveIntensityFour :
  Cobordism.attractorCoherentIntensity
    (Cobordism.alignedUnit ∷ Cobordism.alignedUnit ∷ [])
  ≡ + 4
twoAlignedBranchesHaveIntensityFour = refl

twoAlignedBranchesHavePositiveFluxTwo :
  Cobordism.signedAttractorFlux
    (Cobordism.alignedUnit ∷ Cobordism.alignedUnit ∷ [])
  ≡ + 2
twoAlignedBranchesHavePositiveFluxTwo = refl

twoOpposedBranchesAlsoHaveMagnitudeFour :
  Cobordism.attractorCoherentIntensity
    (Cobordism.opposedUnit ∷ Cobordism.opposedUnit ∷ [])
  ≡ + 4
twoOpposedBranchesAlsoHaveMagnitudeFour = refl

twoOpposedBranchesHaveNegativeFluxTwo :
  Cobordism.signedAttractorFlux
    (Cobordism.opposedUnit ∷ Cobordism.opposedUnit ∷ [])
  ≡ -[1+ 1 ]
twoOpposedBranchesHaveNegativeFluxTwo = refl

intensityAloneDoesNotDetermineAttractorDirection :
  Cobordism.attractorCoherentIntensity
    (Cobordism.alignedUnit ∷ Cobordism.alignedUnit ∷ [])
  ≡
  Cobordism.attractorCoherentIntensity
    (Cobordism.opposedUnit ∷ Cobordism.opposedUnit ∷ [])
intensityAloneDoesNotDetermineAttractorDirection = refl

------------------------------------------------------------------------
-- Which-path memory regressions.
------------------------------------------------------------------------

indistinguishableInPhasePathsRetainInterference :
  Cobordism.markedPairIntensity
    Cobordism.indistinguishablePaths
    Interference.phase0
    Interference.phase0
  ≡ + 4
indistinguishableInPhasePathsRetainInterference = refl

distinguishableInPhasePathsSuppressCrossTerm :
  Cobordism.markedPairIntensity
    Cobordism.distinguishablePaths
    Interference.phase0
    Interference.phase0
  ≡ + 2
distinguishableInPhasePathsSuppressCrossTerm = refl

distinguishableOpposedPathsSuppressCancellation :
  Cobordism.markedPairIntensity
    Cobordism.distinguishablePaths
    Interference.phase0
    Interference.phase2
  ≡ + 2
distinguishableOpposedPathsSuppressCancellation = refl

pathErasureCanCreateTwoUnitsOfSpuriousCoherence :
  Cobordism.markedPairIntensity
    Cobordism.distinguishablePaths
    Interference.phase0
    Interference.phase0
  +ℤ (+ 2)
  ≡
  Cobordism.markedPairIntensity
    Cobordism.indistinguishablePaths
    Interference.phase0
    Interference.phase0
pathErasureCanCreateTwoUnitsOfSpuriousCoherence = refl

------------------------------------------------------------------------
-- Branch marginality and pair-count regressions.
------------------------------------------------------------------------

branchMarginalRegression :
  (branch : Interference.BranchWave) →
  (others : List Interference.BranchWave) →
  Interference.coherentIntensity (branch ∷ others)
  ≡
  (Norm.waveNormSq branch +ℤ Interference.coherentIntensity others)
  +ℤ Interference.pairInterferenceWith branch others
branchMarginalRegression = Cobordism.branchMarginalLaw

threeBranchesHaveThreePairRelations :
  Cobordism.pairRelationCount
    (Interference.phase0 ∷ Interference.phase1 ∷ Interference.phase2 ∷ [])
  ≡ 3
threeBranchesHaveThreePairRelations = refl

fourBranchesHaveSixPairRelations :
  Cobordism.pairRelationCount
    (Interference.phase0
      ∷ Interference.phase1
      ∷ Interference.phase2
      ∷ Interference.phase3
      ∷ [])
  ≡ 6
fourBranchesHaveSixPairRelations = refl

------------------------------------------------------------------------
-- PNF integration regressions.
------------------------------------------------------------------------

pnfGeometryPreservesSplitResidual :
  Integration.preservesSplitRecombineResidual
    Integration.canonicalPNFGeometryCompressionInvariant
  ≡ true
pnfGeometryPreservesSplitResidual = refl

pnfGeometryPreservesInterferenceRelevantMarkers :
  Integration.preservesPathMarkersWhenTheyChangeInterference
    Integration.canonicalPNFGeometryCompressionInvariant
  ≡ true
pnfGeometryPreservesInterferenceRelevantMarkers = refl

pnfGeometryDoesNotInferContinuousAngles :
  Integration.doesNotInferContinuousAnglesFromTrits
    Integration.canonicalPNFGeometryCompressionInvariant
  ≡ true
pnfGeometryDoesNotInferContinuousAngles = refl
