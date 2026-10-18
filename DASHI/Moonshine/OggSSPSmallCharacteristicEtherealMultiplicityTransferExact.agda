module DASHI.Moonshine.OggSSPSmallCharacteristicEtherealMultiplicityTransferExact where

------------------------------------------------------------------------
-- ETHEREAL MODULAR-FORM MULTIPLICITY: POSITIVE BUT INSUFFICIENT TRANSFER
--
-- SOURCE THEOREM
--
-- Kobin--Zureick-Brown Theorem 4.13:
--
--   characteristic 2:
--     2^r tame mu_2 stacky points collide into 2^(r-1) wild Z/2 points,
--     producing 2^(r-1) linearly independent ethereal forms in weight 2;
--
--   characteristic 3:
--     2^s tame mu_3 stacky points collide into 2^(s-1) wild Z/3 points,
--     producing 2^(s-1) linearly independent ethereal forms in weight 2.
--
-- Thus wild stack geometry DOES have a sourced additive multiplicity theorem
-- for a modular-form observable.
--
-- But the multiplicity is one form per wild collision point.  The theorem does
-- not state:
--
--   number of Artin--Schreier layers x number of inertia/local sectors.
--
-- Consequently it is evidence that a geometric correction mechanism exists,
-- but it cannot inhabit WildLayerSectorValuationAuthority.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSPSmallCharacteristicWildLayerSectorProductCandidateExact as LayerSector
import DASHI.Moonshine.OggSSPSmallCharacteristicWildRiemannRochTransferCutsetExact as WildRR
import DASHI.Moonshine.OggSSPSmallCharacteristicWildStackCorrectionConjectureExact as WildSource
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Source-native multiplicity shape.
------------------------------------------------------------------------

record EtherealCollisionMultiplicity : Set where
  constructor ethereal-collision-multiplicity
  field
    tameStackyPointCount : Nat
    wildCollisionPointCount : Nat
    weightTwoEtherealDimension : Nat

    oneEtherealFormPerWildCollision :
      weightTwoEtherealDimension ≡ wildCollisionPointCount

open EtherealCollisionMultiplicity public

------------------------------------------------------------------------
-- 2. The theorem's observable and the Monster-correction observable differ.
------------------------------------------------------------------------

data EtherealWeightTwoDimensionIsMonsterValuation : Set where
data OneFormPerWildPointImpliesOneCopyPerLayerPerSector : Set where
data Theorem413SuppliesLayerSectorValuationAuthority : Set where

etherealDimensionIsNotPromotedToMonsterValuation :
  EtherealWeightTwoDimensionIsMonsterValuation -> ⊥
etherealDimensionIsNotPromotedToMonsterValuation ()

oneFormPerWildPointDoesNotImplyLayerSectorRule :
  OneFormPerWildPointImpliesOneCopyPerLayerPerSector -> ⊥
oneFormPerWildPointDoesNotImplyLayerSectorRule ()

theorem413DoesNotSupplyLayerSectorAuthority :
  Theorem413SuppliesLayerSectorValuationAuthority -> ⊥
theorem413DoesNotSupplyLayerSectorAuthority ()

------------------------------------------------------------------------
-- 3. Positive transfer receipt.
------------------------------------------------------------------------

record EtherealMultiplicityTransferBoundary : Set where
  constructor ethereal-multiplicity-transfer-boundary
  field
    wildGeometryCreatesModularFormDimensionCorrection : Bool
    oneEtherealFormPerWildCollisionPointSourced : Bool
    theoremIsGenuinelyWild : Bool
    theoremUsesArtinSchreierStackGeometryContext : Bool

    theoremCountsArtinSchreierLayersPerSector : Bool
    theoremCountsInertiaSectorsPerLayer : Bool
    theoremProducesMonsterPadicValuation : Bool
    theoremClosesWildLayerSectorAuthority : Bool

    positiveMechanisticPrecedentRetained : Bool
    unsupportedPromotionBlocked : Bool

canonicalEtherealMultiplicityTransferBoundary :
  EtherealMultiplicityTransferBoundary
canonicalEtherealMultiplicityTransferBoundary =
  ethereal-multiplicity-transfer-boundary
    true true true true
    false false false false
    true true

wildLayerSectorBoundary :
  LayerSector.WildLayerSectorProductBoundary
wildLayerSectorBoundary =
  LayerSector.canonicalWildLayerSectorProductBoundary

wildRiemannRochBoundary :
  WildRR.WildRiemannRochTransferCutsetBoundary
wildRiemannRochBoundary =
  WildRR.canonicalWildRiemannRochTransferCutsetBoundary

wildSourceAtlas = WildSource.wildStackCorrectionSourceAtlas

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryFormalReconstruction
