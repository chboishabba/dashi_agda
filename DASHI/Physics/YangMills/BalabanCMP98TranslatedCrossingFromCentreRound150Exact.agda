{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98TranslatedCrossingFromCentreRound150Exact where

------------------------------------------------------------------------
-- ROUND150 A1 BIDI: POINTWISE EQ. (119) CROSSING FROM ONE CENTRE TRANSLATION
--
-- Primary source:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
--
-- Round147 still accepted an x-indexed source equality saying that the chosen
-- one-bond crossing from the c- block hits the corresponding x' in the c+
-- block.  That is stronger source data than the literal periodic geometry
-- needs.  Coordinate translations already commute in the existing centred
-- contour carrier.  Hence one fixed coarse crossing of block centres transports
-- EVERY centred offset by the same crossing.
--
-- This file proves exactly that reduction.  In particular, `plusOffset` may be
-- the identity and the Round147 pointwise field follows from only:
--
--   * one signed crossing direction at the source scale;
--   * c+ = one crossing step from c-; and
--   * the already-isolated periodic coordinate-translation commutation law.
--
-- No x-indexed crossing receipt remains at this layer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Word
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Blocks
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered

------------------------------------------------------------------------
-- A signed periodic one-step direction as a length-one contour segment.
------------------------------------------------------------------------

periodicAxisToContour : Carrier.Axis4 → Contours.Axis4
periodicAxisToContour Carrier.zeroᵢ = Contours.axis0
periodicAxisToContour (Carrier.sucᵢ Carrier.zeroᵢ) = Contours.axis1
periodicAxisToContour (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ)) = Contours.axis2
periodicAxisToContour
  (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ))) = Contours.axis3

unitSegment : Word.SignedAxis4 → Contours.AxisSegment
unitSegment (Carrier.pair axis true) =
  Contours.axisSegment
    (periodicAxisToContour axis)
    (Contours.signedCount Contours.positive (suc zero))
unitSegment (Carrier.pair axis false) =
  Contours.axisSegment
    (periodicAxisToContour axis)
    (Contours.signedCount Contours.negative (suc zero))

unitSegmentWordExact : ∀ direction →
  Periodic.segmentWord (unitSegment direction) ≡ direction ∷ []
unitSegmentWordExact (Carrier.pair Carrier.zeroᵢ true) = refl
unitSegmentWordExact (Carrier.pair Carrier.zeroᵢ false) = refl
unitSegmentWordExact
  (Carrier.pair (Carrier.sucᵢ Carrier.zeroᵢ) true) = refl
unitSegmentWordExact
  (Carrier.pair (Carrier.sucᵢ Carrier.zeroᵢ) false) = refl
unitSegmentWordExact
  (Carrier.pair (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ)) true) = refl
unitSegmentWordExact
  (Carrier.pair (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ)) false) = refl
unitSegmentWordExact
  (Carrier.pair
    (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ))) true) = refl
unitSegmentWordExact
  (Carrier.pair
    (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ))) false) = refl

walkUnitSegmentExact :
  ∀ {n} (site : Blocks.PeriodicBlock n) direction →
  Bond.walk site (Periodic.segmentWord (unitSegment direction))
  ≡ Bond.walkStep site direction
walkUnitSegmentExact site direction
  rewrite unitSegmentWordExact direction = refl

------------------------------------------------------------------------
-- One coordinate segment commutes through an arbitrary finite contour.
------------------------------------------------------------------------

segmentCommutesAcrossContour :
  ∀ {n}
    (commutation : Embed.PeriodicSegmentCommutation n)
    start crossing segments →
  Bond.walk
    (Bond.walk start (Periodic.contourWord segments))
    (Periodic.segmentWord crossing)
  ≡
  Bond.walk
    (Bond.walk start (Periodic.segmentWord crossing))
    (Periodic.contourWord segments)
segmentCommutesAcrossContour commutation start crossing [] = refl
segmentCommutesAcrossContour commutation start crossing (segment ∷ segments) =
  trans
    (cong
      (λ site → Bond.walk site (Periodic.segmentWord crossing))
      (Embed.walkAppend start
        (Periodic.segmentWord segment)
        (Periodic.contourWord segments)))
    (trans
      (segmentCommutesAcrossContour commutation
        (Bond.walk start (Periodic.segmentWord segment))
        crossing segments)
      (trans
        (cong
          (λ site → Bond.walk site (Periodic.contourWord segments))
          (Embed.translationsCommute commutation start segment crossing))
        (sym
          (Embed.walkAppend
            (Bond.walk start (Periodic.segmentWord crossing))
            (Periodic.segmentWord segment)
            (Periodic.contourWord segments)))))

------------------------------------------------------------------------
-- The canonical centred target commutes with a one-bond translation.
------------------------------------------------------------------------

centeredTargetCommutesWithOneStep :
  ∀ {n radius}
    (commutation : Embed.PeriodicSegmentCommutation n)
    (start : Blocks.PeriodicBlock n)
    (point : Centered.CenteredBlockPoint4 radius)
    direction →
  Bond.walkStep (Embed.centeredTargetSite start point) direction
  ≡ Embed.centeredTargetSite (Bond.walkStep start direction) point
centeredTargetCommutesWithOneStep commutation start point direction =
  trans
    (sym (walkUnitSegmentExact (Embed.centeredTargetSite start point) direction))
    (trans
      (segmentCommutesAcrossContour commutation start (unitSegment direction)
        (Contours.activeSegments (Embed.centeredDisplacement4 point)))
      (cong
        (λ site → Bond.walk site (Embed.canonicalCenteredContourWord point))
        (walkUnitSegmentExact start direction)))

------------------------------------------------------------------------
-- Source-facing geometry: one crossing of centres, not one receipt per x.
------------------------------------------------------------------------

record TranslatedNeighbourBlockCrossing (n radius : Nat) : Set₁ where
  field
    commutation : Embed.PeriodicSegmentCommutation n
    minusEmbedding plusEmbedding : Embed.CenteredPeriodicNoWrapEmbedding n radius
    crossingDirection : Word.SignedAxis4

    plusCentreIsOneCrossing :
      Bond.walkStep
        (Embed.embeddingCentre minusEmbedding)
        crossingDirection
      ≡ Embed.embeddingCentre plusEmbedding

open TranslatedNeighbourBlockCrossing public

translatedCrossingHitsSameOffset :
  ∀ {n radius}
    (geometry : TranslatedNeighbourBlockCrossing n radius)
    point →
  Bond.walkStep
    (Embed.embed (minusEmbedding geometry) point)
    (crossingDirection geometry)
  ≡ Embed.embed (plusEmbedding geometry) point
translatedCrossingHitsSameOffset geometry point =
  trans
    (cong
      (λ site → Bond.walkStep site (crossingDirection geometry))
      (Embed.embedMeaning (minusEmbedding geometry) point))
    (trans
      (centeredTargetCommutesWithOneStep
        (commutation geometry)
        (Embed.embeddingCentre (minusEmbedding geometry))
        point
        (crossingDirection geometry))
      (trans
        (cong
          (λ centre → Embed.centeredTargetSite centre point)
          (plusCentreIsOneCrossing geometry))
        (sym (Embed.embedMeaning (plusEmbedding geometry) point))))

-- Exact specialization matching Round147's physical radius-six crossing field:
-- crossingDirection is point-independent and plusOffset is definitionally the
-- same centred coordinate.
radiusSixTranslatedCrossingHitsSameOffset :
  ∀ {n}
    (geometry : TranslatedNeighbourBlockCrossing n 6)
    point →
  Bond.walkStep
    (Embed.embed (minusEmbedding geometry) point)
    (crossingDirection geometry)
  ≡ Embed.embed (plusEmbedding geometry) point
radiusSixTranslatedCrossingHitsSameOffset = translatedCrossingHitsSameOffset

cmp98TranslatedCrossingFromCentreCompilerRound150Level : ProofLevel
cmp98TranslatedCrossingFromCentreCompilerRound150Level = machineChecked

-- Remaining physical geometry is no longer x-indexed.  It is the source
-- identification of one neighbouring coarse-block centre crossing together
-- with the already-existing periodic translation-commutation input.
literalCMP98CoarseCentreCrossingIdentificationRound150Level : ProofLevel
literalCMP98CoarseCentreCrossingIdentificationRound150Level = conditional
