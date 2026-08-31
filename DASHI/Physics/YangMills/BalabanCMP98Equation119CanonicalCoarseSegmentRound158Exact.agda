{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact where

------------------------------------------------------------------------
-- ROUND158 A1 BIDI: REMOVE THE ARBITRARY COARSE AxisSegment RECEIPT
--
-- Primary source:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
--
-- R152 still accepts an arbitrary `AxisSegment` for the source coarse bond c.
-- At the minimal source scale used by this Eq. (119) lane we have L = 13 and
-- radius = 6, hence the fine realization of one coarse axis bond is the straight
-- signed segment of length 13.  BIDI therefore keeps only the source axis and
-- orientation and CONSTRUCTS the segment count.
--
-- Cross-pollination update: R162 proves periodic coordinate-translation
-- commutation directly from the repository's finite-torus successor/predecessor
-- arithmetic.  Therefore this source record no longer contains a
-- `translationCommutation` receipt either.
--
-- This does not manufacture the remaining physical statement that the selected
-- c-/c+ centres are related by that source bond: the endpoint equality remains
-- explicit.  It removes only replaceable geometry choices.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119LeastPrivilegeSourceRound152Exact as R152
import DASHI.Physics.YangMills.BalabanPeriodicSegmentCommutationRound162Exact as R162
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Blocks
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Word

sourceL : Nat
sourceL = 13

sourceRadius : Nat
sourceRadius = 6

sourceSideFromRadius : Nat
sourceSideFromRadius = 13

sourceSideIsL : sourceSideFromRadius ≡ sourceL
sourceSideIsL = refl

canonicalCoarseSegment : Contours.Axis4 → Contours.Direction → Contours.AxisSegment
canonicalCoarseSegment axis direction =
  Contours.axisSegment axis (Contours.signedCount direction sourceL)

record CanonicalL13Equation119Source
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
      Nat → Embed.CenteredPeriodicNoWrapEmbedding n sourceRadius

    coarseAxis : Nat → Contours.Axis4
    coarseDirection : Nat → Contours.Direction

    canonicalCoarseSegmentEndsAtPlusCentre : ∀ step →
      Bond.walk
        (Embed.embeddingCentre (minusEmbedding step))
        (Periodic.segmentWord
          (canonicalCoarseSegment (coarseAxis step) (coarseDirection step)))
      ≡ Embed.embeddingCentre (plusEmbedding step)

open CanonicalL13Equation119Source public

asRound152Source :
  ∀ {C n Value group} →
  CanonicalL13Equation119Source C n Value group →
  R152.LiteralEquation119LeastPrivilegeSource C n Value group
asRound152Source {n = n} source = record
  { R152.LiteralEquation119LeastPrivilegeSource.realization = realization source
  ; R152.LiteralEquation119LeastPrivilegeSource.bondComponent = bondComponent source
  ; R152.LiteralEquation119LeastPrivilegeSource.adjointLink = adjointLink source
  ; R152.LiteralEquation119LeastPrivilegeSource.scaleV = scaleV source
  ; R152.LiteralEquation119LeastPrivilegeSource.qSource = qSource source
  ; R152.LiteralEquation119LeastPrivilegeSource.minusEmbedding = minusEmbedding source
  ; R152.LiteralEquation119LeastPrivilegeSource.plusEmbedding = plusEmbedding source
  ; R152.LiteralEquation119LeastPrivilegeSource.coarseSegment =
      λ step → canonicalCoarseSegment
        (coarseAxis source step) (coarseDirection source step)
  ; R152.LiteralEquation119LeastPrivilegeSource.coarseSegmentEndsAtPlusCentre =
      canonicalCoarseSegmentEndsAtPlusCentre source
  ; R152.LiteralEquation119LeastPrivilegeSource.translationCommutation =
      R162.periodicSegmentCommutation n
  }

round152CoarseSegmentIsCanonicalL13 :
  ∀ {C n Value group}
    (source : CanonicalL13Equation119Source C n Value group)
    step →
  R152.coarseSegment (asRound152Source source) step
  ≡ canonicalCoarseSegment
      (coarseAxis source step) (coarseDirection source step)
round152CoarseSegmentIsCanonicalL13 source step = refl

round152CoarseSegmentCountIsL :
  ∀ {C n Value group}
    (source : CanonicalL13Equation119Source C n Value group)
    step →
  Contours.segmentCount (R152.coarseSegment (asRound152Source source) step)
  ≡ Contours.signedCount (coarseDirection source step) sourceL
round152CoarseSegmentCountIsL source step = refl

round152TranslationCommutationIsDerived :
  ∀ {C n Value group}
    (source : CanonicalL13Equation119Source C n Value group) →
  R152.translationCommutation (asRound152Source source)
  ≡ R162.periodicSegmentCommutation n
round152TranslationCommutationIsDerived source = refl

cmp98Equation119CanonicalCoarseSegmentRound158Level : ProofLevel
cmp98Equation119CanonicalCoarseSegmentRound158Level = machineChecked

cmp98Equation119DerivedTranslationCommutationRound158Level : ProofLevel
cmp98Equation119DerivedTranslationCommutationRound158Level = machineChecked

-- The arbitrary segment shape/count and translation-commutation receipt are gone.
-- The surviving physical geometry is only: which source coordinate
-- axis/orientation is c, and that its canonical L=13 translate really connects
-- the selected c- and c+ centres.
literalCMP98CoarseAxisOrientationRound158Level : ProofLevel
literalCMP98CoarseAxisOrientationRound158Level = conditional

literalCMP98CanonicalL13CentreEndpointRound158Level : ProofLevel
literalCMP98CanonicalL13CentreEndpointRound158Level = conditional
