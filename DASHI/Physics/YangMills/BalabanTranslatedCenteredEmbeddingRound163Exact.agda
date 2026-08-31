{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanTranslatedCenteredEmbeddingRound163Exact where

------------------------------------------------------------------------
-- ROUND163 BIDI / CROSS-POLLINATION:
-- THE PLUS BLOCK EMBEDDING IS A TRANSLATE, NOT AN INDEPENDENT RECEIPT
--
-- CMP98 Eq. (14) uses x(c): the point with the SAME centred coordinate in the
-- neighbouring block reached by translating through the coarse bond c.
-- R158 still accepted independent minus/plus centred embeddings plus a centre
-- endpoint equality.  That is more freedom than the source geometry has.
--
-- R162 proves coordinate translations commute on the literal periodic torus;
-- the periodic inverse-path owner proves every translation word is invertible.
-- Together these construct the translated embedding itself, including its
-- meaning, injectivity, and origin theorem.  Hence a downstream Eq. (119) source
-- needs only ONE centred embedding and the coarse translation word.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicSegmentCommutationRound162Exact as R162
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicPathInverseBianchiExact as InversePath
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicCoordinateClosureExact as Closure
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed

translatedEmbedding :
  ∀ {n radius} →
  Embed.CenteredPeriodicNoWrapEmbedding n radius →
  Contours.AxisSegment →
  Embed.CenteredPeriodicNoWrapEmbedding n radius
translatedEmbedding {n} embedding segment = record
  { Embed.CenteredPeriodicNoWrapEmbedding.embeddingCentre =
      Bond.walk
        (Embed.embeddingCentre embedding)
        (Periodic.segmentWord segment)
  ; Embed.CenteredPeriodicNoWrapEmbedding.embed =
      λ point → Bond.walk
        (Embed.embed embedding point)
        (Periodic.segmentWord segment)
  ; Embed.CenteredPeriodicNoWrapEmbedding.embedMeaning =
      λ point →
        trans
          (cong
            (λ start → Bond.walk start (Periodic.segmentWord segment))
            (Embed.embedMeaning embedding point))
          (R162.walkWordsCommute
            (Embed.embeddingCentre embedding)
            (Embed.canonicalCenteredContourWord point)
            (Periodic.segmentWord segment))
  ; Embed.CenteredPeriodicNoWrapEmbedding.embedInjective =
      λ {left} {right} translatedEqual →
        Embed.embedInjective embedding
          (trans
            (sym
              (InversePath.walkReverseOpposite
                (Closure.periodicStepInverseLaws n)
                (Embed.embed embedding left)
                (Periodic.segmentWord segment)))
            (trans
              (cong
                (λ site → Bond.walk site
                  (InversePath.reverseOpposite (Periodic.segmentWord segment)))
                translatedEqual)
              (InversePath.walkReverseOpposite
                (Closure.periodicStepInverseLaws n)
                (Embed.embed embedding right)
                (Periodic.segmentWord segment))))
  ; Embed.CenteredPeriodicNoWrapEmbedding.originMeaning =
      cong
        (λ start → Bond.walk start (Periodic.segmentWord segment))
        (Embed.originMeaning embedding)
  }

translatedCentreExact :
  ∀ {n radius}
    (embedding : Embed.CenteredPeriodicNoWrapEmbedding n radius)
    segment →
  Embed.embeddingCentre (translatedEmbedding embedding segment)
  ≡ Bond.walk (Embed.embeddingCentre embedding) (Periodic.segmentWord segment)
translatedCentreExact embedding segment = Agda.Builtin.Equality.refl

translatedPointExact :
  ∀ {n radius}
    (embedding : Embed.CenteredPeriodicNoWrapEmbedding n radius)
    segment point →
  Embed.embed (translatedEmbedding embedding segment) point
  ≡ Bond.walk (Embed.embed embedding point) (Periodic.segmentWord segment)
translatedPointExact embedding segment point = Agda.Builtin.Equality.refl

translatedCenteredEmbeddingRound163Level : ProofLevel
translatedCenteredEmbeddingRound163Level = machineChecked

translatedCenteredEmbeddingInjectivityRound163Level : ProofLevel
translatedCenteredEmbeddingInjectivityRound163Level = machineChecked

-- This removes independent plus-block embedding/endpoint data wherever the
-- physical source says the plus block is literally the coarse translate of the
-- minus block.
