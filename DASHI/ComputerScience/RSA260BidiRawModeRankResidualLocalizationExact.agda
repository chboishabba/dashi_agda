module DASHI.ComputerScience.RSA260BidiRawModeRankResidualLocalizationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Core.CoarseFineRelativeFibreExact as Fibre
import DASHI.Core.ConsumerIndexedResidualLocalizationExact as Localization
import DASHI.ComputerScience.RSA260BidiFactorLayerStructureCollisionExact as Factor
import DASHI.ComputerScience.RSA260BidiCoefficientRankPrefixFrontierExact as Rank
import DASHI.ComputerScience.RSA260BidiGeneratorDigestPrefixFrontierExact as Digest

------------------------------------------------------------------------
-- LOCALIZE THE ROTATE3/AFFINE7 DIFFERENCE INSIDE THE RAW-MODE RESIDUAL
--
-- FactorLayerStructureCollision established that rotate3 and affine7 have the
-- same factor-mode footprint, selected bases and masks.  Their first two
-- coefficient ranks are both zero, but the first complementary raw-mode layer
-- F_2 already separates them:
--
--   rotate3 : rank(F_2) = 7
--   affine7 : rank(F_2) = 5
--
-- This is a strictly smaller witness-level coordinate than the whole recovered
-- generator identity.  It is not claimed globally adequate or minimal.
------------------------------------------------------------------------

data RawCollisionWorld : Set where
  rotate3RawWorld : RawCollisionWorld
  affine7RawWorld : RawCollisionWorld

factorStructureCoarse : RawCollisionWorld -> Factor.FactorLayerStructure
factorStructureCoarse rotate3RawWorld = Factor.rotate3FactorStructure
factorStructureCoarse affine7RawWorld = Factor.rotate3FactorStructure

rawResidual : RawCollisionWorld -> RawCollisionWorld
rawResidual world = world

reopenRawCollision :
  Factor.FactorLayerStructure -> RawCollisionWorld -> RawCollisionWorld
reopenRawCollision _ residual = residual

reopenRawCollisionExact :
  (world : RawCollisionWorld) ->
  reopenRawCollision (factorStructureCoarse world) (rawResidual world) ≡ world
reopenRawCollisionExact rotate3RawWorld = refl
reopenRawCollisionExact affine7RawWorld = refl

rawCollisionGeometry : Fibre.CoarseFineReopening RawCollisionWorld
rawCollisionGeometry =
  Fibre.coarseFineReopening
    Factor.FactorLayerStructure
    RawCollisionWorld
    factorStructureCoarse
    rawResidual
    reopenRawCollision
    reopenRawCollisionExact

receiptObserve : RawCollisionWorld -> Digest.GeneratorReceiptAnswer
receiptObserve rotate3RawWorld = Digest.rotate3Receipt
receiptObserve affine7RawWorld = Digest.affine7Receipt

receiptFineSensitive :
  Fibre.FineSensitiveConsumer rawCollisionGeometry receiptObserve
receiptFineSensitive =
  Fibre.fineSensitiveConsumer
    rotate3RawWorld
    affine7RawWorld
    refl
    (λ ())
    "rotate3/affine7: identical formal factor-layer structure, distinct recovered generator receipt identity"

------------------------------------------------------------------------
-- Smaller residual coordinate: rank of first RAW layer F_2.
------------------------------------------------------------------------

data FirstRawLayerRank : Set where
  rankFive : FirstRawLayerRank
  rankSeven : FirstRawLayerRank

firstRawLayerRank : RawCollisionWorld -> FirstRawLayerRank
firstRawLayerRank rotate3RawWorld = rankSeven
firstRawLayerRank affine7RawWorld = rankFive

firstRawLayerRankSeparates :
  firstRawLayerRank rotate3RawWorld ≡ firstRawLayerRank affine7RawWorld -> ⊥
firstRawLayerRankSeparates ()

rawResidualLocalization :
  Localization.LocalizedResidualWitness rawCollisionGeometry receiptObserve
rawResidualLocalization =
  Localization.localized-residual-witness
    receiptFineSensitive
    FirstRawLayerRank
    firstRawLayerRank
    firstRawLayerRankSeparates

localizedObserverSeparatesRotate3Affine7 :
  Localization.localizedObserver rawResidualLocalization rotate3RawWorld
  ≡ Localization.localizedObserver rawResidualLocalization affine7RawWorld
  -> ⊥
localizedObserverSeparatesRotate3Affine7 =
  Localization.localizedObserverSeparatesWitness rawResidualLocalization

------------------------------------------------------------------------
-- Weld to the already-owned coefficient-rank evidence.
------------------------------------------------------------------------

rotate3FourLayerRankReceipt :
  Rank.fourLayerRankObserve Digest.rotate3World ≡ Rank.r17-0-0-7-7
rotate3FourLayerRankReceipt = refl

affine7FourLayerRankReceipt :
  Rank.fourLayerRankObserve Digest.affine7World ≡ Rank.r17-0-0-5-7
affine7FourLayerRankReceipt = refl

factorStructureEqualityInherited :
  Factor.rotate3FactorStructure ≡ Factor.affine7FactorStructure
factorStructureEqualityInherited = Factor.rotate3Affine7SameFactorStructure

------------------------------------------------------------------------
-- Boundary / next residual.
------------------------------------------------------------------------

record RawModeRankResidualLocalizationBoundary : Set where
  constructor raw-mode-rank-residual-localization-boundary
  field
    commonResidualLocalizationKernelReused : Bool
    factorLayerStructureCollisionInherited : Bool
    firstComplementaryRawLayerIsF2 : Bool
    rotate3F2RankIsSeven : Bool
    affine7F2RankIsFive : Bool
    firstRawLayerRankSeparatesConcreteWitness : Bool
    fullRawPayloadNeededToSeparateThisWitness : Bool
    firstRawRankGloballyDeterminesGeneratorIdentity : Bool
    firstRawRankProvedMinimalResidual : Bool
    rawBytesReconstructedHere : Bool
    productionRSA260Claimed : Bool
open RawModeRankResidualLocalizationBoundary public

canonicalRawModeRankResidualLocalizationBoundary :
  RawModeRankResidualLocalizationBoundary
canonicalRawModeRankResidualLocalizationBoundary =
  raw-mode-rank-residual-localization-boundary
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false

data RawModeRankResidual : Set where
  attackFirstRawRankAcrossWiderCollisionFamily : RawModeRankResidual
  refineRawLayerRankIntoRowSpaceAndPayloadResidual : RawModeRankResidual
  searchRawPrefixConsumerTerminal : RawModeRankResidual
  retainFullRawPayloadOnlyIfFinerConsumerRequiresIt : RawModeRankResidual
  recurseUntilConsumerOrExactTerminal : RawModeRankResidual

firstRawModeRankResidual : RawModeRankResidual
firstRawModeRankResidual = attackFirstRawRankAcrossWiderCollisionFamily
