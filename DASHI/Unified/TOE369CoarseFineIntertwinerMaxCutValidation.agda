{-# OPTIONS --safe #-}
module DASHI.Unified.TOE369CoarseFineIntertwinerMaxCutValidation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Unifier as Legacy
import DASHI.Unified.TOE369CoarseFineIntertwinerMaxCutExact as TOE
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369CoarseFineFabricAdapterExact as Fabric
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Spectral
import DASHI.Moonshine.Base369Ternary27SignedSymmetryMonsterIntertwinerExact as Signed

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
