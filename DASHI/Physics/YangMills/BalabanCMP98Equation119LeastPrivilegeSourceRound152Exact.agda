{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119LeastPrivilegeSourceRound152Exact where

------------------------------------------------------------------------
-- ROUND152 A1 BIDI: LEAST-PRIVILEGE SOURCE DATA FOR CMP98 EQ. (119)
--
-- Primary source:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
--
-- CMP98 Eq. (14) and Eq. (119) use the translated coarse-bond segment
-- `[x,x(c)]`.  R147/R150 now derive that entire x-indexed family from ONE
-- source coarse axis segment c and periodic segment commutation.  R148/R149
-- separately force the Lie-calculus fields to the already-owned dexp family.
--
-- Therefore the public source record below contains neither:
--   * pointwise x -> x(c) endpoint receipts;
--   * independently chosen path words;
--   * fresh g/g^-1/adjoint operators; nor
--   * a scalar Q' receipt.
--
-- A caller supplies the physical background/perturbation data, the two literal
-- centred embeddings, one coarse signed segment joining their centres, and the
-- existing periodic translation-commutation input.  The dexp convention is a
-- separate already-owned producer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralPathRound147Exact as R147
import DASHI.Physics.YangMills.BalabanCMP98Equation119DexpReuseRound148Exact as R148
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
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

    -- The literal coarse bond c.  Its fine word is generated from this segment.
    coarseSegment : Nat → Contours.AxisSegment

    coarseSegmentEndsAtPlusCentre : ∀ step →
      Bond.walk
        (Embed.embeddingCentre (minusEmbedding step))
        (Periodic.segmentWord (coarseSegment step))
      ≡ Embed.embeddingCentre (plusEmbedding step)

    -- Existing repository geometry needed to commute the translated coarse
    -- segment through the centred coordinate contour.
    translationCommutation : Embed.PeriodicSegmentCommutation n

open LiteralEquation119LeastPrivilegeSource public

-- Strong constructor: no replaceable x-indexed crossing or Lie-calculus field
-- appears in the source input type.
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
  ; R147.LiteralEquation119PathData.coarseSegment = coarseSegment source
  ; R147.LiteralEquation119PathData.coarseSegmentEndsAtPlusCentre =
      coarseSegmentEndsAtPlusCentre source
  ; R147.LiteralEquation119PathData.translationCommutation =
      translationCommutation source
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

-- The pointwise source-leg equality is now a theorem of the producer.
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

-- Exact surviving source seams:
--   (1) source coarse bond c is this concrete signed fine-lattice axis segment
--       (including its physical length/orientation and endpoint);
--   (2) CMP98 printed Y/Y_x is the existing left/right dexp convention.
literalCMP98CoarseSegmentIdentificationRound152Level : ProofLevel
literalCMP98CoarseSegmentIdentificationRound152Level = conditional

-- Compatibility status name retained for older dashboards.
literalCMP98CentreBondIdentificationRound152Level : ProofLevel
literalCMP98CentreBondIdentificationRound152Level =
  literalCMP98CoarseSegmentIdentificationRound152Level

literalCMP98PrintedDexpConventionRound152Level : ProofLevel
literalCMP98PrintedDexpConventionRound152Level = conditional
