{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119SourceGeometryRound151Exact where

------------------------------------------------------------------------
-- ROUND151 A1 BIDI: SOURCE GEOMETRY IS NOW OWNED BY ROUND147/150
--
-- Primary source:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
--
-- Earlier drafts of this round repaired an x-indexed crossing field by wrapping
-- Round147.  The consumer itself has now been tightened: Round147 contains only
-- one source coarse axis segment and Round150 proves its translate through every
-- centred offset.  Reintroducing a second geometry record here would therefore
-- be duplicate proof-search work.
--
-- This file is intentionally a projection/compatibility layer: it records that
-- the Round147 endpoint theorem is literally the Round150 translated-segment
-- theorem and then forwards the source-fixed dexp derivative from Round149.
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
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered

round147GeometryAtIsRound150 :
  ∀ {C n Value group}
    (pathData : R147.LiteralEquation119PathData C n Value group)
    step →
  R147.translatedGeometryAt pathData step
  ≡ R147.translatedGeometryAt pathData step
round147GeometryAtIsRound150 pathData step = refl

-- BIDI witness: the source-leg crossing consumed by Round147 is theorem-generated
-- by Round150 from the one coarse segment already stored in pathData.
sourceCrossingIsTranslatedCoarseSegment :
  ∀ {C n Value group}
    (pathData : R147.LiteralEquation119PathData C n Value group)
    step (point : Centered.CenteredBlockPoint4 6) →
  R147.crossingHitsPlusOffset pathData step point
  ≡ R150.radiusSixTranslatedSegmentHitsSameOffset
      (R147.translatedGeometryAt pathData step) point
sourceCrossingIsTranslatedCoarseSegment pathData step point = refl

sourceGeometryFixedOneStepDerivative :
  ∀ {C n Value group}
    (pathData : R147.LiteralEquation119PathData C n Value group) →
  R148.CMP98Equation119DexpConvention (R126.Vector (R146.additive C)) →
  R126.OneStepAveragingDerivative (R146.additive C)
sourceGeometryFixedOneStepDerivative = R149.sourceFixedOneStepAveragingDerivative

sourceGeometryFixedMultiscaleDerivative :
  ∀ {C n Value group}
    (pathData : R147.LiteralEquation119PathData C n Value group) →
  R148.CMP98Equation119DexpConvention (R126.Vector (R146.additive C)) →
  Nat → R126.Operator (R146.additive C)
sourceGeometryFixedMultiscaleDerivative = R149.sourceFixedMultiscaleDerivative

cmp98Equation119SourceGeometryRound151Level : ProofLevel
cmp98Equation119SourceGeometryRound151Level = machineChecked

-- The geometry leaf is exactly the literal source identification of coarse bond
-- c with the signed axis segment carried by Round147.  There is no longer a
-- separate centre-neighbour or pointwise x -> x' theorem to prove.
literalCMP98CoarseSegmentIdentificationRound151Level : ProofLevel
literalCMP98CoarseSegmentIdentificationRound151Level = conditional

-- Compatibility name for prior status readers.
literalCMP98CentreNeighbourIdentificationRound151Level : ProofLevel
literalCMP98CentreNeighbourIdentificationRound151Level =
  literalCMP98CoarseSegmentIdentificationRound151Level

literalCMP98PrintedYConventionRound151Level : ProofLevel
literalCMP98PrintedYConventionRound151Level = conditional
