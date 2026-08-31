{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119SourceGeometryRound151Exact where

------------------------------------------------------------------------
-- ROUND151 A1 BIDI: REMOVE THE x-INDEXED CROSSING RECEIPT FROM THE CONSUMER
--
-- Primary source:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
--
-- CMP98 Eq. (14) defines the averaging contour as
--
--   Gamma_{c-,x} union [x,x(c)] union Gamma_{x(c),c+},
--
-- an oriented contour from c- to c+.  Eq. (119) differentiates the same
-- one-step geometry.  Round147 encoded the translated crossing pointwise.
-- Round150 proves that, on the repository periodic carrier, one centre
-- translation transports every centred offset by the same one-bond step.
--
-- This file makes that theorem the actual Round147 producer.  The old
-- point-indexed `crossingHitsPlusOffset` field of the supplied path carrier is
-- deliberately ignored.  The produced carrier instead has:
--
--   crossingDirection step point = one source centre direction,
--   plusOffset step point         = point,
--   crossingHitsPlusOffset        = Round150 translated-crossing theorem.
--
-- Thus the Eq. (119) consumer no longer depends on one crossing receipt per x.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralPathRound147Exact as R147
import DASHI.Physics.YangMills.BalabanCMP98Equation119DexpReuseRound148Exact as R148
import DASHI.Physics.YangMills.BalabanCMP98Equation119SourceFixedDexpRound149Exact as R149
import DASHI.Physics.YangMills.BalabanCMP98TranslatedCrossingFromCentreRound150Exact as R150
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Word

record CentreTranslatedCMP98Crossing {C n Value group}
    (pathData : R147.LiteralEquation119PathData C n Value group) : Set₁ where
  field
    commutation : Embed.PeriodicSegmentCommutation n
    direction : Nat → Word.SignedAxis4
    plusCentreIsOneCrossing : ∀ step →
      Bond.walkStep
        (Embed.embeddingCentre (R147.minusEmbedding pathData step))
        (direction step)
      ≡ Embed.embeddingCentre (R147.plusEmbedding pathData step)

open CentreTranslatedCMP98Crossing public

translatedGeometry :
  ∀ {C n Value group}
    {pathData : R147.LiteralEquation119PathData C n Value group} →
  CentreTranslatedCMP98Crossing pathData → Nat →
  R150.TranslatedNeighbourBlockCrossing n 6
translatedGeometry {pathData = pathData} crossing step = record
  { R150.TranslatedNeighbourBlockCrossing.commutation = commutation crossing
  ; R150.TranslatedNeighbourBlockCrossing.minusEmbedding =
      R147.minusEmbedding pathData step
  ; R150.TranslatedNeighbourBlockCrossing.plusEmbedding =
      R147.plusEmbedding pathData step
  ; R150.TranslatedNeighbourBlockCrossing.crossingDirection = direction crossing step
  ; R150.TranslatedNeighbourBlockCrossing.plusCentreIsOneCrossing =
      plusCentreIsOneCrossing crossing step
  }

withCentreTranslatedCrossing :
  ∀ {C n Value group}
    (pathData : R147.LiteralEquation119PathData C n Value group) →
  CentreTranslatedCMP98Crossing pathData →
  R147.LiteralEquation119PathData C n Value group
withCentreTranslatedCrossing pathData crossing = record
  { R147.LiteralEquation119PathData.realization = R147.realization pathData
  ; R147.LiteralEquation119PathData.bondComponent = R147.bondComponent pathData
  ; R147.LiteralEquation119PathData.adjointLink = R147.adjointLink pathData
  ; R147.LiteralEquation119PathData.scaleV = R147.scaleV pathData
  ; R147.LiteralEquation119PathData.qSource = R147.qSource pathData
  ; R147.LiteralEquation119PathData.minusEmbedding = R147.minusEmbedding pathData
  ; R147.LiteralEquation119PathData.plusEmbedding = R147.plusEmbedding pathData
  ; R147.LiteralEquation119PathData.coarseWord = R147.coarseWord pathData
  ; R147.LiteralEquation119PathData.coarseWordEndsAtPlusCentre =
      R147.coarseWordEndsAtPlusCentre pathData
  ; R147.LiteralEquation119PathData.crossingDirection =
      λ step _ → direction crossing step
  ; R147.LiteralEquation119PathData.plusOffset = λ _ point → point
  ; R147.LiteralEquation119PathData.crossingHitsPlusOffset =
      λ step point →
        R150.radiusSixTranslatedCrossingHitsSameOffset
          (translatedGeometry crossing step) point
  ; R147.LiteralEquation119PathData.dexpMinusOuter = R147.dexpMinusOuter pathData
  ; R147.LiteralEquation119PathData.inverseDexpMinusAt = R147.inverseDexpMinusAt pathData
  ; R147.LiteralEquation119PathData.adjointExpAt = R147.adjointExpAt pathData
  ; R147.LiteralEquation119PathData.adjointExpOuter = R147.adjointExpOuter pathData
  }

-- BIDI witness: the produced x -> x' crossing is definitionally driven by the
-- centre-translation geometry, not by the old pointwise field in `pathData`.
centreTranslatedCrossingIsRound150 :
  ∀ {C n Value group}
    (pathData : R147.LiteralEquation119PathData C n Value group)
    (crossing : CentreTranslatedCMP98Crossing pathData)
    step point →
  R147.crossingHitsPlusOffset
    (withCentreTranslatedCrossing pathData crossing) step point
  ≡ R150.radiusSixTranslatedCrossingHitsSameOffset
      (translatedGeometry crossing step) point
centreTranslatedCrossingIsRound150 pathData crossing step point = refl

sourceGeometryFixedOneStepDerivative :
  ∀ {C n Value group}
    (pathData : R147.LiteralEquation119PathData C n Value group) →
  CentreTranslatedCMP98Crossing pathData →
  R148.CMP98Equation119DexpConvention (R126.Vector (R146.additive C)) →
  R126.OneStepAveragingDerivative (R146.additive C)
sourceGeometryFixedOneStepDerivative pathData crossing convention =
  R149.sourceFixedOneStepAveragingDerivative
    (withCentreTranslatedCrossing pathData crossing) convention

sourceGeometryFixedMultiscaleDerivative :
  ∀ {C n Value group}
    (pathData : R147.LiteralEquation119PathData C n Value group) →
  CentreTranslatedCMP98Crossing pathData →
  R148.CMP98Equation119DexpConvention (R126.Vector (R146.additive C)) →
  Nat → R126.Operator (R146.additive C)
sourceGeometryFixedMultiscaleDerivative pathData crossing convention =
  R126.multiscaleAveragePrime
    (sourceGeometryFixedOneStepDerivative pathData crossing convention)

cmp98Equation119SourceGeometryRound151Level : ProofLevel
cmp98Equation119SourceGeometryRound151Level = machineChecked

-- The translated-crossing leaf has now collapsed to one centre-neighbour
-- identification per scale.  The remaining Lie-facing leaf is still the literal
-- CMP98 printed Y/Y_x sign/trivialisation identification with the reused dexp
-- family; no new g/g^-1/Q' data is introduced.
literalCMP98CentreNeighbourIdentificationRound151Level : ProofLevel
literalCMP98CentreNeighbourIdentificationRound151Level = conditional

literalCMP98PrintedYConventionRound151Level : ProofLevel
literalCMP98PrintedYConventionRound151Level = conditional
