{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119LeastPrivilegeSourceRound152Exact where

------------------------------------------------------------------------
-- ROUND152 A1 BIDI: LEAST-PRIVILEGE SOURCE DATA FOR CMP98 EQ. (119)
--
-- Primary source:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
--
-- R147 was deliberately general enough to expose both pointwise crossing data
-- and four Lie-calculus operators.  R149 and R151 proved that those fields can
-- be replaced by stronger existing producers.  This file closes the BIDI loop:
-- the PUBLIC source record no longer contains either family of replaceable
-- receipts.
--
-- A caller supplies only:
--   * the actual periodic background realization and perturbation projection;
--   * the literal centered embeddings and coarse contour;
--   * ONE neighbouring-centre crossing per scale plus coordinate commutation;
--   * the source q itself and exact additive/scalar operations.
--
-- The dexp/inverse-dexp/adjoint family is supplied separately through the
-- already-owned R148 convention.  From these inputs we construct the R147
-- carrier, hence Eq. (119), hence the R126 multiscale derivative.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralPathRound147Exact as R147
import DASHI.Physics.YangMills.BalabanCMP98Equation119DexpReuseRound148Exact as R148
import DASHI.Physics.YangMills.BalabanCMP98TranslatedCrossingFromCentreRound150Exact as R150
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Blocks
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Word

record LiteralEquation119LeastPrivilegeSource
    (C : R146.SignedAdditiveOperatorCarrier)
    (n : Nat)
    (Value : Set)
    (group : Bond.ExactLinkGroup Value) : Set₁ where
  field
    realization : Nat → Bond.PeriodicBondGaugeRealization n Value group

    bondComponent :
      Nat → R126.Vector (R146.additive C) →
      Blocks.PeriodicBlock n → Word.SignedAxis4 →
      R126.Vector (R146.additive C)

    adjointLink : Nat → Value → R126.Operator (R146.additive C)
    scaleV : ℚ → R126.Operator (R146.additive C)
    qSource : Nat → R126.Operator (R146.additive C)

    minusEmbedding plusEmbedding :
      Nat → Embed.CenteredPeriodicNoWrapEmbedding n 6

    coarseWord : Nat → List Word.SignedAxis4
    coarseWordEndsAtPlusCentre : ∀ step →
      Bond.walk
        (Embed.embeddingCentre (minusEmbedding step))
        (coarseWord step)
      ≡ Embed.embeddingCentre (plusEmbedding step)

    -- The only crossing information: one translation of block centres.
    commutation : Embed.PeriodicSegmentCommutation n
    crossingDirection : Nat → Word.SignedAxis4
    plusCentreIsOneCrossing : ∀ step →
      Bond.walkStep
        (Embed.embeddingCentre (minusEmbedding step))
        (crossingDirection step)
      ≡ Embed.embeddingCentre (plusEmbedding step)

open LiteralEquation119LeastPrivilegeSource public

translatedGeometry :
  ∀ {C n Value group} →
  LiteralEquation119LeastPrivilegeSource C n Value group → Nat →
  R150.TranslatedNeighbourBlockCrossing n 6
translatedGeometry source step = record
  { R150.TranslatedNeighbourBlockCrossing.commutation = commutation source
  ; R150.TranslatedNeighbourBlockCrossing.minusEmbedding = minusEmbedding source step
  ; R150.TranslatedNeighbourBlockCrossing.plusEmbedding = plusEmbedding source step
  ; R150.TranslatedNeighbourBlockCrossing.crossingDirection =
      crossingDirection source step
  ; R150.TranslatedNeighbourBlockCrossing.plusCentreIsOneCrossing =
      plusCentreIsOneCrossing source step
  }

-- Strong constructor: the obsolete x-indexed crossing receipt and arbitrary
-- Lie-calculus fields never occur in this function's input type.
asLiteralPathData :
  ∀ {C n Value group} →
  LiteralEquation119LeastPrivilegeSource C n Value group →
  R148.CMP98Equation119DexpConvention (R126.Vector (R146.additive C)) →
  R147.LiteralEquation119PathData C n Value group
asLiteralPathData source convention = record
  { R147.LiteralEquation119PathData.realization = realization source
  ; R147.LiteralEquation119PathData.bondComponent = bondComponent source
  ; R147.LiteralEquation119PathData.adjointLink = adjointLink source
  ; R147.LiteralEquation119PathData.scaleV = scaleV source
  ; R147.LiteralEquation119PathData.qSource = qSource source
  ; R147.LiteralEquation119PathData.minusEmbedding = minusEmbedding source
  ; R147.LiteralEquation119PathData.plusEmbedding = plusEmbedding source
  ; R147.LiteralEquation119PathData.coarseWord = coarseWord source
  ; R147.LiteralEquation119PathData.coarseWordEndsAtPlusCentre =
      coarseWordEndsAtPlusCentre source
  ; R147.LiteralEquation119PathData.crossingDirection =
      λ step _ → crossingDirection source step
  ; R147.LiteralEquation119PathData.plusOffset = λ _ point → point
  ; R147.LiteralEquation119PathData.crossingHitsPlusOffset =
      λ step point →
        R150.radiusSixTranslatedCrossingHitsSameOffset
          (translatedGeometry source step) point
  ; R147.LiteralEquation119PathData.dexpMinusOuter =
      R148.outerDexpMinus convention
  ; R147.LiteralEquation119PathData.inverseDexpMinusAt =
      R148.pointInverseDexpMinus convention
  ; R147.LiteralEquation119PathData.adjointExpAt =
      R148.pointAdjointExp convention
  ; R147.LiteralEquation119PathData.adjointExpOuter =
      R148.outerAdjointExp convention
  }

leastPrivilegeEquation119QPrime :
  ∀ {C n Value group} →
  LiteralEquation119LeastPrivilegeSource C n Value group →
  R148.CMP98Equation119DexpConvention (R126.Vector (R146.additive C)) →
  Nat → R126.Operator (R146.additive C)
leastPrivilegeEquation119QPrime source convention =
  R147.literalEquation119QPrime (asLiteralPathData source convention)

leastPrivilegeOneStepDerivative :
  ∀ {C n Value group} →
  LiteralEquation119LeastPrivilegeSource C n Value group →
  R148.CMP98Equation119DexpConvention (R126.Vector (R146.additive C)) →
  R126.OneStepAveragingDerivative (R146.additive C)
leastPrivilegeOneStepDerivative source convention =
  R147.asLiteralOneStepAveragingDerivative (asLiteralPathData source convention)

leastPrivilegeMultiscaleDerivative :
  ∀ {C n Value group} →
  LiteralEquation119LeastPrivilegeSource C n Value group →
  R148.CMP98Equation119DexpConvention (R126.Vector (R146.additive C)) →
  Nat → R126.Operator (R146.additive C)
leastPrivilegeMultiscaleDerivative source convention =
  R126.multiscaleAveragePrime (leastPrivilegeOneStepDerivative source convention)

-- The pointwise source leg equality is now a theorem of the producer.
derivedSourceLegsShareEndpoint :
  ∀ {C n Value group}
    (source : LiteralEquation119LeastPrivilegeSource C n Value group)
    (convention : R148.CMP98Equation119DexpConvention
      (R126.Vector (R146.additive C)))
    step (point : Centered.CenteredBlockPoint4 6) →
  Bond.walk
    (Embed.embeddingCentre (minusEmbedding source step))
    (R147.minusToCrossingWord (asLiteralPathData source convention) step point)
  ≡ Bond.walk
      (Embed.embeddingCentre (minusEmbedding source step))
      (R147.plusFullWord (asLiteralPathData source convention) step point)
derivedSourceLegsShareEndpoint source convention =
  R147.sourceLegsShareEndpoint (asLiteralPathData source convention)

cmp98Equation119LeastPrivilegeSourceRound152Level : ProofLevel
cmp98Equation119LeastPrivilegeSourceRound152Level = machineChecked

-- At this interface the only source-facing mathematical identifications left
-- are genuinely literal ones: which centre-neighbour bond is CMP98's c-/c+
-- crossing, and which existing left/right dexp convention is the printed Y/Yx
-- convention.  No pointwise crossing, fresh g/g^-1, or scalar Q' receipt exists.
literalCMP98CentreBondIdentificationRound152Level : ProofLevel
literalCMP98CentreBondIdentificationRound152Level = conditional

literalCMP98PrintedDexpConventionRound152Level : ProofLevel
literalCMP98PrintedDexpConventionRound152Level = conditional
