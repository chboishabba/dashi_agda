{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralPathRound147Exact where

------------------------------------------------------------------------
-- ROUND147 A1 BIDI MEETING POINT: ACTUAL CMP98 EQ. (119) PATH REALIZATION
--
-- Primary source:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
--
-- Round146 represented Eq. (119), but still accepted its three R0-path legs as
-- arbitrary operators.  This file removes that loophole.  R0 A is constructed
-- recursively on the repository's actual signed periodic bond words:
--
--   (R0 A)(d :: F)
--     = A_d + Ad_{U_d} ((R0 A)(F)),
--
-- where U_d is literally `Bond.orientedLink` at the current walked site.
--
-- Source correction from CMP98: the middle leg `[x,x(c)]` is the TRANSLATE of
-- the coarse bond c through x.  It is not assumed to be one fine-lattice bond.
-- We therefore represent c by one signed axis segment and use its generated
-- finite `segmentWord` in BOTH occurrences:
--
--   F_{c-,x} ++ word(c)
--   word(c) ++ F_{c+,x(c)}.
--
-- Round150 proves these two orders have the same endpoint from periodic segment
-- commutation.  Thus the old x-indexed crossing receipt and independent x'
-- offset are both gone.
--
-- The block sum runs over `Centered.centeredBlockFinite 6`, so its source side
-- and volume reduce definitionally to 13 and 28561.  The exact CMP98 weight is
-- therefore 1/28561.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (_++_)
open import Data.Rational.Base as ℚ using (ℚ; _/_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98TranslatedCrossingFromCentreRound150Exact as R150
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Blocks
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Word

------------------------------------------------------------------------
-- Exact minimal source scale used by the CMP98/CMP109 local block.
------------------------------------------------------------------------

radiusSixSideExact : Centered.centeredBlockDisplayedSide 6 ≡ 13
radiusSixSideExact = refl

radiusSixVolumeExact : Centered.centeredBlockDisplayedVolume 6 ≡ 28561
radiusSixVolumeExact = refl

siteWeightℚ : ℚ
siteWeightℚ = + 1 / 28561

------------------------------------------------------------------------
-- Source data which cannot be manufactured by the path compiler.
------------------------------------------------------------------------

record LiteralEquation119PathData
    (C : R146.SignedAdditiveOperatorCarrier)
    (n : Nat)
    (Value : Set)
    (group : Bond.ExactLinkGroup Value) : Set₁ where
  field
    -- Actual periodic background link realization at every one-step scale.
    realization : Nat → Bond.PeriodicBondGaugeRealization n Value group

    -- One global perturbation vector is projected to the literal oriented bond
    -- component used by R0.  This is a representation/projection map, not an
    -- independently supplied path value.
    bondComponent :
      Nat → R126.Vector (R146.additive C) →
      Blocks.PeriodicBlock n → Word.SignedAxis4 →
      R126.Vector (R146.additive C)

    -- Adjoint action of the ACTUAL oriented background link on the Lie carrier.
    adjointLink :
      Nat → Value → R126.Operator (R146.additive C)

    -- Exact scalar multiplication on the additive Lie carrier.  Round147 uses
    -- this only at the fixed source value 1/28561.
    scaleV : ℚ → R126.Operator (R146.additive C)

    -- The literal one-step average itself; only its derivative is constructed
    -- here from Eq. (119).
    qSource : Nat → R126.Operator (R146.additive C)

    -- Two actual centered no-wrap block embeddings at the neighbouring source
    -- centres c- and c+.
    minusEmbedding plusEmbedding :
      Nat → Embed.CenteredPeriodicNoWrapEmbedding n 6

    -- Source coarse bond c, represented by ONE signed straight segment.  Its
    -- fine path is generated by `Periodic.segmentWord`; no independent path
    -- word may disagree with the source segment.
    coarseSegment : Nat → Contours.AxisSegment

    coarseSegmentEndsAtPlusCentre : ∀ step →
      Bond.walk
        (Embed.embeddingCentre (minusEmbedding step))
        (Periodic.segmentWord (coarseSegment step))
      ≡ Embed.embeddingCentre (plusEmbedding step)

    -- Existing periodic coordinate-translation commutation.  Round150 uses it
    -- to translate c through every x in B(c-) and derives x(c) automatically.
    translationCommutation : Embed.PeriodicSegmentCommutation n

    -- Existing dexp/adjoint operators after the literal CMP98 sign and
    -- trivialisation convention has been identified.  These are NOT path
    -- operators and are deliberately the only Lie-calculus seam left here.
    dexpMinusOuter : Nat → R126.Operator (R146.additive C)
    inverseDexpMinusAt :
      Nat → Centered.CenteredBlockPoint4 6 →
      R126.Operator (R146.additive C)
    adjointExpAt :
      Nat → Centered.CenteredBlockPoint4 6 →
      R126.Operator (R146.additive C)
    adjointExpOuter : Nat → R126.Operator (R146.additive C)

open LiteralEquation119PathData public

------------------------------------------------------------------------
-- Derived coarse word and translated point x(c).
------------------------------------------------------------------------

coarseWord :
  ∀ {C n Value group} →
  LiteralEquation119PathData C n Value group →
  Nat → List Word.SignedAxis4
coarseWord dataSet step = Periodic.segmentWord (coarseSegment dataSet step)

plusOffset :
  ∀ {C n Value group} →
  LiteralEquation119PathData C n Value group →
  Nat → Centered.CenteredBlockPoint4 6 → Centered.CenteredBlockPoint4 6
plusOffset dataSet step point = point

translatedGeometryAt :
  ∀ {C n Value group} →
  LiteralEquation119PathData C n Value group →
  Nat → R150.TranslatedNeighbourBlockSegment n 6
translatedGeometryAt dataSet step = record
  { R150.TranslatedNeighbourBlockSegment.commutation =
      translationCommutation dataSet
  ; R150.TranslatedNeighbourBlockSegment.minusEmbedding =
      minusEmbedding dataSet step
  ; R150.TranslatedNeighbourBlockSegment.plusEmbedding =
      plusEmbedding dataSet step
  ; R150.TranslatedNeighbourBlockSegment.coarseSegment =
      coarseSegment dataSet step
  ; R150.TranslatedNeighbourBlockSegment.plusCentreIsCoarseSegment =
      coarseSegmentEndsAtPlusCentre dataSet step
  }

crossingHitsPlusOffset :
  ∀ {C n Value group}
    (dataSet : LiteralEquation119PathData C n Value group)
    step point →
  Bond.walk
    (Embed.embed (minusEmbedding dataSet step) point)
    (coarseWord dataSet step)
  ≡ Embed.embed (plusEmbedding dataSet step) (plusOffset dataSet step point)
crossingHitsPlusOffset dataSet step point =
  R150.radiusSixTranslatedSegmentHitsSameOffset
    (translatedGeometryAt dataSet step) point

------------------------------------------------------------------------
-- Actual R0 recursion on signed periodic bonds.
------------------------------------------------------------------------

r0Path :
  ∀ {C n Value group} →
  LiteralEquation119PathData C n Value group →
  Nat → R126.Vector (R146.additive C) →
  Blocks.PeriodicBlock n → List Word.SignedAxis4 →
  R126.Vector (R146.additive C)
r0Path dataSet step A site [] = R126.zeroV (R146.additive _)
r0Path {C} dataSet step A site (direction ∷ directions) =
  R126.addV (R146.additive C)
    (bondComponent dataSet step A site direction)
    (adjointLink dataSet step
      (Bond.orientedLink (realization dataSet step) site direction)
      (r0Path dataSet step A
        (Bond.walkStep site direction) directions))

------------------------------------------------------------------------
-- Literal source words from centered-block geometry.
------------------------------------------------------------------------

minusToCrossingWord :
  ∀ {C n Value group} →
  LiteralEquation119PathData C n Value group →
  Nat → Centered.CenteredBlockPoint4 6 → List Word.SignedAxis4
minusToCrossingWord dataSet step point =
  Embed.canonicalCenteredContourWord point
  ++ coarseWord dataSet step

plusFullWord :
  ∀ {C n Value group} →
  LiteralEquation119PathData C n Value group →
  Nat → Centered.CenteredBlockPoint4 6 → List Word.SignedAxis4
plusFullWord dataSet step point =
  coarseWord dataSet step
  ++ Embed.canonicalCenteredContourWord (plusOffset dataSet step point)

centreWord :
  ∀ {C n Value group} →
  LiteralEquation119PathData C n Value group → Nat → List Word.SignedAxis4
centreWord = coarseWord

-- The first concatenation terminates at the translated point x(c).
minusToCrossingEndpointExact :
  ∀ {C n Value group}
    (dataSet : LiteralEquation119PathData C n Value group)
    step point →
  Bond.walk
    (Embed.embeddingCentre (minusEmbedding dataSet step))
    (minusToCrossingWord dataSet step point)
  ≡ Bond.walk
      (Embed.embed (minusEmbedding dataSet step) point)
      (coarseWord dataSet step)
minusToCrossingEndpointExact dataSet step point =
  trans
    (Embed.walkAppend
      (Embed.embeddingCentre (minusEmbedding dataSet step))
      (Embed.canonicalCenteredContourWord point)
      (coarseWord dataSet step))
    (cong
      (λ site → Bond.walk site (coarseWord dataSet step))
      (sym (Embed.embedMeaning (minusEmbedding dataSet step) point)))

-- The second concatenation also terminates at the same selected plus-block x(c).
plusFullEndpointExact :
  ∀ {C n Value group}
    (dataSet : LiteralEquation119PathData C n Value group)
    step point →
  Bond.walk
    (Embed.embeddingCentre (minusEmbedding dataSet step))
    (plusFullWord dataSet step point)
  ≡ Embed.embed (plusEmbedding dataSet step) (plusOffset dataSet step point)
plusFullEndpointExact dataSet step point =
  trans
    (Embed.walkAppend
      (Embed.embeddingCentre (minusEmbedding dataSet step))
      (coarseWord dataSet step)
      (Embed.canonicalCenteredContourWord (plusOffset dataSet step point)))
    (trans
      (cong
        (λ site →
          Bond.walk site
            (Embed.canonicalCenteredContourWord (plusOffset dataSet step point)))
        (coarseSegmentEndsAtPlusCentre dataSet step))
      (sym
        (Embed.embedMeaning
          (plusEmbedding dataSet step)
          (plusOffset dataSet step point))))

-- Hence both printed Eq. (119) legs land at the same literal x(c).
sourceLegsShareEndpoint :
  ∀ {C n Value group}
    (dataSet : LiteralEquation119PathData C n Value group)
    step point →
  Bond.walk
    (Embed.embeddingCentre (minusEmbedding dataSet step))
    (minusToCrossingWord dataSet step point)
  ≡ Bond.walk
      (Embed.embeddingCentre (minusEmbedding dataSet step))
      (plusFullWord dataSet step point)
sourceLegsShareEndpoint dataSet step point =
  trans
    (minusToCrossingEndpointExact dataSet step point)
    (trans
      (crossingHitsPlusOffset dataSet step point)
      (sym (plusFullEndpointExact dataSet step point)))

------------------------------------------------------------------------
-- Exact finite block sum of the literal R0 legs.
------------------------------------------------------------------------

pointTerm :
  ∀ {C n Value group} →
  LiteralEquation119PathData C n Value group →
  Nat → R126.Vector (R146.additive C) →
  Centered.CenteredBlockPoint4 6 →
  R126.Vector (R146.additive C)
pointTerm {C} dataSet step A point =
  scaleV dataSet siteWeightℚ
    (inverseDexpMinusAt dataSet step point
      (R146.subV
        (r0Path dataSet step A
          (Embed.embeddingCentre (minusEmbedding dataSet step))
          (minusToCrossingWord dataSet step point))
        (adjointExpAt dataSet step point
          (r0Path dataSet step A
            (Embed.embeddingCentre (minusEmbedding dataSet step))
            (plusFullWord dataSet step point)))))

pointTerms :
  ∀ {C n Value group} →
  LiteralEquation119PathData C n Value group →
  Nat → R126.Vector (R146.additive C) →
  List (Centered.CenteredBlockPoint4 6) →
  List (R126.Vector (R146.additive C))
pointTerms dataSet step A [] = []
pointTerms dataSet step A (point ∷ points) =
  pointTerm dataSet step A point ∷ pointTerms dataSet step A points

literalBlockContribution :
  ∀ {C n Value group} →
  LiteralEquation119PathData C n Value group →
  Nat → R126.Vector (R146.additive C) →
  R126.Vector (R146.additive C)
literalBlockContribution dataSet step A =
  R146.sumV
    (pointTerms dataSet step A
      (Carrier.elements (Centered.centeredBlockFinite 6)))

literalEquation119QPrime :
  ∀ {C n Value group} →
  LiteralEquation119PathData C n Value group →
  Nat → R126.Operator (R146.additive C)
literalEquation119QPrime {C} dataSet step A =
  R126.addV (R146.additive C)
    (dexpMinusOuter dataSet step (literalBlockContribution dataSet step A))
    (adjointExpOuter dataSet step
      (r0Path dataSet step A
        (Embed.embeddingCentre (minusEmbedding dataSet step))
        (centreWord dataSet step)))

------------------------------------------------------------------------
-- Direct R126 producer: no scalar or abstract path-valued Q' receipt remains.
------------------------------------------------------------------------

asLiteralOneStepAveragingDerivative :
  ∀ {C n Value group} →
  LiteralEquation119PathData C n Value group →
  R126.OneStepAveragingDerivative (R146.additive C)
asLiteralOneStepAveragingDerivative dataSet = record
  { R126.OneStepAveragingDerivative.q = qSource dataSet
  ; R126.OneStepAveragingDerivative.qPrime = literalEquation119QPrime dataSet
  }

literalOneStepDerivativeIsConstructedEquation119 :
  ∀ {C n Value group}
    (dataSet : LiteralEquation119PathData C n Value group)
    step A →
  R126.qPrime (asLiteralOneStepAveragingDerivative dataSet) step A
  ≡ literalEquation119QPrime dataSet step A
literalOneStepDerivativeIsConstructedEquation119 dataSet step A = refl

literalEquation119MultiscaleDerivative :
  ∀ {C n Value group} →
  LiteralEquation119PathData C n Value group →
  Nat → R126.Operator (R146.additive C)
literalEquation119MultiscaleDerivative dataSet =
  R126.multiscaleAveragePrime (asLiteralOneStepAveragingDerivative dataSet)

cmp98Equation119LiteralR0PathCompilerRound147Level : ProofLevel
cmp98Equation119LiteralR0PathCompilerRound147Level = machineChecked

cmp98Equation119RadiusSixFiniteBlockRound147Level : ProofLevel
cmp98Equation119RadiusSixFiniteBlockRound147Level = machineChecked

cmp98Equation119ExactWeightRound147Level : ProofLevel
cmp98Equation119ExactWeightRound147Level = machineChecked

cmp98Equation119TranslatedCrossingFromCentreRound147Level : ProofLevel
cmp98Equation119TranslatedCrossingFromCentreRound147Level = machineChecked

-- The former x-indexed translated-crossing field is gone.  Remaining physical
-- geometry is one source coarse-bond -> signed-axis-segment identification plus
-- the already-isolated periodic translation-commutation input.
literalCMP98CoarseSegmentIdentificationRound147Level : ProofLevel
literalCMP98CoarseSegmentIdentificationRound147Level = conditional

-- Compatibility name for older status readers.
literalCMP98TranslatedCrossingIdentificationRound147Level : ProofLevel
literalCMP98TranslatedCrossingIdentificationRound147Level =
  literalCMP98CoarseSegmentIdentificationRound147Level

literalCMP98DexpConventionIdentificationRound147Level : ProofLevel
literalCMP98DexpConventionIdentificationRound147Level = conditional
