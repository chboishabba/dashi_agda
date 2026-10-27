{-# OPTIONS --safe #-}
module DASHI.Unified.TOE369CoarseFineIntertwinerMaxCutExact where

------------------------------------------------------------------------
-- ZKP O/R/C/S/L/P/G/F
--
-- O. Objective.
-- Connect the canonical 369 coarse/fine and ternary symmetry owners to the
-- focused DASHI TOE graph.
--
-- R. Reuse.
-- Reuse Base369CoarseFineFabricAdapterExact for exact coarse/fine reopening.
-- Reuse Base369Ternary27SpectralSymmetryIrrepBridgeExact for C3 rotation.
-- Reuse Base369Ternary27SignedSymmetryMonsterIntertwinerExact for the exact
-- phase-conjugation intertwiner.
-- Reuse the existing validation modules for non-promotion theorems.
--
-- C. Construction.
-- Add one exact chart between the concrete legacy Unifier trit and SSPTrit.
-- No Unifier axiom-shaped theorem is used as proof authority.
--
-- S. Safety invariants.
-- The 27-state cube is not a free C3 torsor because the origin is fixed.
-- The signed ternary symmetry is not promoted to a Monster representation.
-- Base369 is an instance of the coarse/fine fabric, not the generic fabric.
-- A shared C3 shape is not a physical same-object theorem.
--
-- L. Lane.
-- This module owns only the 369 coarse/fine and ternary TOE normalization.
-- It does not edit ESD or digital_esd modules.
-- It does not copy code from meta-introspector repositories.
--
-- P. Postconditions.
-- TOE consumers get one normalized surface for the exact coarse/fine reopening,
-- the ternary C3 action, the Monster phase-conjugation intertwiner, and the
-- exact non-promotion boundaries.
--
-- G. Governance.
-- Original theorem owners retain proof ownership.
-- The legacy Unifier carrier is treated as a carrier only.
--
-- F. Verification.
-- Source read-back checks exact imports and theorem names.
-- Kernel certification requires an exact-head Agda or CI receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Unifier as Legacy
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.InvolutiveTernaryExistingSpineBridge as Involutive
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369CoarseFineFabricAdapterExact as Fabric
import DASHI.Core.CoarseFineRelativeFibreExact as Fibre
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Spectral
import DASHI.Moonshine.Base369Ternary27SignedSymmetryMonsterIntertwinerExact as Signed
import DASHI.Base369Ternary27SpectralGeometryValidation as SpectralValidation
import DASHI.Core.CoarseFineFabricCalculusRegression as CoarseValidation

------------------------------------------------------------------------
-- 1. Legacy Unifier ternary carrier <-> canonical SSP trit.
--
-- This is a carrier chart only.
-- It does not import any Unifier theorem axiom as authority.
------------------------------------------------------------------------

legacyToSSP : Legacy.T → SSP.SSPTrit
legacyToSSP Legacy.neg = SSP.sspNegOne
legacyToSSP Legacy.zer = SSP.sspZero
legacyToSSP Legacy.pos = SSP.sspPosOne

sspToLegacy : SSP.SSPTrit → Legacy.T
sspToLegacy SSP.sspNegOne = Legacy.neg
sspToLegacy SSP.sspZero = Legacy.zer
sspToLegacy SSP.sspPosOne = Legacy.pos

legacySSPRoundTrip :
  (value : Legacy.T) →
  sspToLegacy (legacyToSSP value) ≡ value
legacySSPRoundTrip Legacy.neg = refl
legacySSPRoundTrip Legacy.zer = refl
legacySSPRoundTrip Legacy.pos = refl

sspLegacyRoundTrip :
  (value : SSP.SSPTrit) →
  legacyToSSP (sspToLegacy value) ≡ value
sspLegacyRoundTrip SSP.sspNegOne = refl
sspLegacyRoundTrip SSP.sspZero = refl
sspLegacyRoundTrip SSP.sspPosOne = refl

legacyInvolutionIntertwines :
  (value : Legacy.T) →
  legacyToSSP (Legacy.ι value)
  ≡ Involutive.sspι (legacyToSSP value)
legacyInvolutionIntertwines Legacy.neg = refl
legacyInvolutionIntertwines Legacy.zer = refl
legacyInvolutionIntertwines Legacy.pos = refl

------------------------------------------------------------------------
-- 2. Canonical coarse/fine reopening.
------------------------------------------------------------------------

toeCoarseFineReopening :
  Fibre.CoarseFineReopening Geometry.TernaryHyperformalPoint
toeCoarseFineReopening = Fabric.base369CoarseFineReopening

toeCoarseFineReopensExactly :
  (state : Geometry.TernaryHyperformalPoint) →
  Fibre.reopen toeCoarseFineReopening
    (Fibre.coarse toeCoarseFineReopening state)
    (Fibre.relativeFine toeCoarseFineReopening state)
  ≡ state
toeCoarseFineReopensExactly =
  Fibre.reopenExact toeCoarseFineReopening

toeCoarseFineObserverSeparating :
  (left right : Geometry.TernaryHyperformalPoint) →
  Fabric.base369CoarseFineObserver left
  ≡ Fabric.base369CoarseFineObserver right →
  left ≡ right
toeCoarseFineObserverSeparating =
  Fabric.base369CoarseFineObserverSeparating

------------------------------------------------------------------------
-- 3. Ternary 27-state C3 and signed phase intertwiner.
------------------------------------------------------------------------

toeTernary27RotationOrderThree :
  (point : Geometry.Ternary27Point) →
  Spectral.rotateXYZ
    (Spectral.rotateXYZ
      (Spectral.rotateXYZ point))
  ≡ point
toeTernary27RotationOrderThree =
  Spectral.rotateXYZOrderThree

toeTernary27OriginFixed :
  Spectral.rotateXYZ Geometry.origin ≡ Geometry.origin
toeTernary27OriginFixed =
  Spectral.originFixedByRotation

toeMonsterPhaseConjugationIntertwiner =
  Signed.monsterAxisReflectionIntertwines

------------------------------------------------------------------------
-- 4. Exact non-promotion boundaries.
------------------------------------------------------------------------

FullCubeRotationFree : Set
FullCubeRotationFree =
  (point : Geometry.Ternary27Point) →
  Spectral.rotateXYZ point ≡ point →
  ⊥

fullCubeRotationIsNotFree :
  FullCubeRotationFree → ⊥
fullCubeRotationIsNotFree free =
  free Geometry.origin toeTernary27OriginFixed

toeFullDFTNotClaimed :
  Spectral.Base369Ternary27SpectralSymmetryBoundary.fullTwentySevenPointDFTConstructed
    Spectral.canonicalBase369Ternary27SpectralSymmetryBoundary
  ≡ false
toeFullDFTNotClaimed =
  SpectralValidation.fullDFTNotClaimed

toeMonsterRepresentationNotClaimed :
  Signed.SignedTernaryVoxelSymmetryBoundary.voxelRepresentationOfMonsterEstablished
    Signed.canonicalSignedTernaryVoxelSymmetryBoundary
  ≡ false
toeMonsterRepresentationNotClaimed =
  SpectralValidation.monsterRepresentationNotClaimed

toeMonsterEmbeddingNotClaimed :
  Signed.SignedTernaryVoxelSymmetryBoundary.signedPermutationGroupEmbeddedInMonster
    Signed.canonicalSignedTernaryVoxelSymmetryBoundary
  ≡ false
toeMonsterEmbeddingNotClaimed =
  SpectralValidation.monsterEmbeddingNotClaimed

toeBase369IsNotGenericFabric :
  Fabric.Base369CoarseFineBoundary.base369IsGenericFabric
    Fabric.canonicalBase369CoarseFineBoundary
  ≡ false
toeBase369IsNotGenericFabric =
  CoarseValidation.base369IsInstanceNotGenericFabric
