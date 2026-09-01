{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98TranslatedCrossingFromCentreRound150Exact where

------------------------------------------------------------------------
-- ROUND150 A1 BIDI: EQ. (119) TRANSLATED COARSE SEGMENT FROM THE CENTRE
--
-- Primary source:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
--
-- Source-faithful correction: CMP98 writes the middle contour leg as
-- `[x,x(c)]`, the translate of the coarse bond c through the fine point x.  It
-- must not be silently strengthened to one fine-lattice bond.  On the literal
-- periodic carrier a coarse bond is represented by one signed AXIS SEGMENT,
-- whose finite `segmentWord` may contain many fine steps (at the minimal source
-- block the eventual physical count is L = 13).
--
-- Round147 previously accepted an x-indexed endpoint receipt.  This file proves
-- that no such family is needed.  Coordinate-segment commutation transports one
-- fixed coarse segment through every canonical centred offset contour:
--
--   walk(embed(c-,p), word(c)) = embed(c+,p)
--
-- whenever the SAME segment sends the c- centre to the c+ centre.  Thus x(c)
-- has the same local centred coordinate p in the neighbouring block.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Blocks
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered

------------------------------------------------------------------------
-- One coordinate segment commutes through an arbitrary finite contour.
------------------------------------------------------------------------

segmentCommutesAcrossContour :
  ∀ {n}
    (commutation : Embed.PeriodicSegmentCommutation n)
    (start : Blocks.PeriodicBlock n)
    crossing segments →
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
-- A translated coarse segment commutes with the canonical centred offset.
------------------------------------------------------------------------

centeredTargetCommutesWithSegment :
  ∀ {n radius}
    (commutation : Embed.PeriodicSegmentCommutation n)
    (start : Blocks.PeriodicBlock n)
    (point : Centered.CenteredBlockPoint4 radius)
    segment →
  Bond.walk
    (Embed.centeredTargetSite start point)
    (Periodic.segmentWord segment)
  ≡
  Embed.centeredTargetSite
    (Bond.walk start (Periodic.segmentWord segment))
    point
centeredTargetCommutesWithSegment commutation start point segment =
  segmentCommutesAcrossContour commutation start segment
    (Contours.activeSegments (Embed.centeredDisplacement4 point))

------------------------------------------------------------------------
-- Source-facing geometry: one coarse segment between centres.
------------------------------------------------------------------------

record TranslatedNeighbourBlockSegment (n radius : Nat) : Set₁ where
  field
    commutation : Embed.PeriodicSegmentCommutation n
    minusEmbedding plusEmbedding : Embed.CenteredPeriodicNoWrapEmbedding n radius

    -- Literal source coarse bond c on the fine periodic carrier.  Its word is
    -- generated, not supplied independently.
    coarseSegment : Contours.AxisSegment

    plusCentreIsCoarseSegment :
      Bond.walk
        (Embed.embeddingCentre minusEmbedding)
        (Periodic.segmentWord coarseSegment)
      ≡ Embed.embeddingCentre plusEmbedding

open TranslatedNeighbourBlockSegment public

translatedSegmentHitsSameOffset :
  ∀ {n radius}
    (geometry : TranslatedNeighbourBlockSegment n radius)
    point →
  Bond.walk
    (Embed.embed (minusEmbedding geometry) point)
    (Periodic.segmentWord (coarseSegment geometry))
  ≡ Embed.embed (plusEmbedding geometry) point
translatedSegmentHitsSameOffset geometry point =
  trans
    (cong
      (λ site →
        Bond.walk site (Periodic.segmentWord (coarseSegment geometry)))
      (Embed.embedMeaning (minusEmbedding geometry) point))
    (trans
      (centeredTargetCommutesWithSegment
        (commutation geometry)
        (Embed.embeddingCentre (minusEmbedding geometry))
        point
        (coarseSegment geometry))
      (trans
        (cong
          (λ centre → Embed.centeredTargetSite centre point)
          (plusCentreIsCoarseSegment geometry))
        (sym (Embed.embedMeaning (plusEmbedding geometry) point))))

radiusSixTranslatedSegmentHitsSameOffset :
  ∀ {n}
    (geometry : TranslatedNeighbourBlockSegment n 6)
    point →
  Bond.walk
    (Embed.embed (minusEmbedding geometry) point)
    (Periodic.segmentWord (coarseSegment geometry))
  ≡ Embed.embed (plusEmbedding geometry) point
radiusSixTranslatedSegmentHitsSameOffset = translatedSegmentHitsSameOffset

cmp98TranslatedCrossingFromCentreCompilerRound150Level : ProofLevel
cmp98TranslatedCrossingFromCentreCompilerRound150Level = machineChecked

-- Remaining physical geometry is no longer x-indexed.  It is the identification
-- of source coarse bond c with one concrete signed fine-lattice axis segment,
-- plus the already-isolated periodic coordinate-translation commutation input.
literalCMP98CoarseSegmentIdentificationRound150Level : ProofLevel
literalCMP98CoarseSegmentIdentificationRound150Level = conditional

-- Compatibility status name retained for Round145 validation/status readers.
literalCMP98CoarseCentreCrossingIdentificationRound150Level : ProofLevel
literalCMP98CoarseCentreCrossingIdentificationRound150Level =
  literalCMP98CoarseSegmentIdentificationRound150Level
