{-# OPTIONS --safe #-}
module DASHI.Unified.TOE369CoarseFineIntertwinerMaxCutValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Unifier as Legacy
import DASHI.Unified.TOE369CoarseFineIntertwinerMaxCutExact as TOE
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369CoarseFineFabricAdapterExact as Fabric
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Spectral
import DASHI.Moonshine.Base369Ternary27SignedSymmetryMonsterIntertwinerExact as Signed
import DASHI.Wikimedia.IbrahimMonster3BRecognitionRouteParetoExact as Pareto
import DASHI.Reasoning.Trialectic369Selected3BSemanticProjectedCompletionExact as Selected3B

legacyNegativeRoundTrip :
  TOE.sspToLegacy (TOE.legacyToSSP Legacy.neg) ≡ Legacy.neg
legacyNegativeRoundTrip = refl

sspPositiveRoundTrip :
  TOE.legacyToSSP (TOE.sspToLegacy SSP.sspPosOne) ≡ SSP.sspPosOne
sspPositiveRoundTrip = refl

originIsFixed :
  Spectral.rotateXYZ Geometry.origin ≡ Geometry.origin
originIsFixed = TOE.toeTernary27OriginFixed

fullRotationCannotBeFree :
  TOE.FullCubeRotationFree → ⊥
fullRotationCannotBeFree = TOE.fullCubeRotationIsNotFree

fullDFTRemainsUnclaimed :
  Spectral.Base369Ternary27SpectralSymmetryBoundary.fullTwentySevenPointDFTConstructed
    Spectral.canonicalBase369Ternary27SpectralSymmetryBoundary ≡ false
fullDFTRemainsUnclaimed = TOE.toeFullDFTNotClaimed

monsterRepresentationRemainsUnclaimed :
  Signed.SignedTernaryVoxelSymmetryBoundary.voxelRepresentationOfMonsterEstablished
    Signed.canonicalSignedTernaryVoxelSymmetryBoundary ≡ false
monsterRepresentationRemainsUnclaimed =
  TOE.toeMonsterRepresentationNotClaimed

monsterEmbeddingRemainsUnclaimed :
  Signed.SignedTernaryVoxelSymmetryBoundary.signedPermutationGroupEmbeddedInMonster
    Signed.canonicalSignedTernaryVoxelSymmetryBoundary ≡ false
monsterEmbeddingRemainsUnclaimed =
  TOE.toeMonsterEmbeddingNotClaimed

base369RemainsAnInstanceNotGenericFabric :
  Fabric.Base369CoarseFineBoundary.base369IsGenericFabric
    Fabric.canonicalBase369CoarseFineBoundary ≡ false
base369RemainsAnInstanceNotGenericFabric =
  TOE.toeBase369IsNotGenericFabric

monsterPhaseIntertwinerRemainsExact :
  Signed.SignedTernaryVoxelSymmetryBoundary.monster3BPhaseInversionMatchesFrequencyConjugation
    Signed.canonicalSignedTernaryVoxelSymmetryBoundary ≡ true
monsterPhaseIntertwinerRemainsExact = refl

actualMonsterActionRecognitionRemainsOpen :
  Pareto.RecognitionRouteParetoBoundary.actualActionRecognitionObserved
    Pareto.canonicalRecognitionRouteParetoBoundary ≡ false
actualMonsterActionRecognitionRemainsOpen =
  TOE.toeMonsterActualActionRecognitionStillOpen

selected3BMinCutHasTwoSourceLeaves :
  Selected3B.Trialectic369Selected3BSemanticProjectedCompletionBoundary.onlyLinearRetractionAndProjectedActionRemain
    Selected3B.canonicalTrialectic369Selected3BSemanticProjectedCompletionBoundary ≡ true
selected3BMinCutHasTwoSourceLeaves =
  TOE.toeSelected3BOnlyRetractionAndProjectedActionRemain

selected3BRetractionRemainsOpen :
  Selected3B.Trialectic369Selected3BSemanticProjectedCompletionBoundary.actualLinearRetractionInhabitedHere
    Selected3B.canonicalTrialectic369Selected3BSemanticProjectedCompletionBoundary ≡ false
selected3BRetractionRemainsOpen =
  TOE.toeSelected3BActualRetractionStillOpen

selected3BProjectedActionRemainsOpen :
  Selected3B.Trialectic369Selected3BSemanticProjectedCompletionBoundary.projectedActionInputInhabitedHere
    Selected3B.canonicalTrialectic369Selected3BSemanticProjectedCompletionBoundary ≡ false
selected3BProjectedActionRemainsOpen =
  TOE.toeSelected3BProjectedActionStillOpen
