{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact where

------------------------------------------------------------------------
-- ROUND158 A1 BIDI: CANONICAL COARSE SEGMENT + DERIVED PLUS BLOCK
--
-- Primary source:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
--
-- At the minimal source scale used by this Eq. (119) lane, L = 13 and radius =
-- 6.  One source coarse axis bond is therefore the straight signed fine segment
-- of length 13.  R162 additionally proves periodic translation commutation from
-- the literal torus arithmetic, and R163 constructs the translated centred
-- embedding itself.
--
-- BIDI consequence: the source record below now supplies only ONE centred block
-- embedding plus the coarse axis/orientation.  The L=13 segment, the plus-block
-- embedding, the c- -> c+ endpoint equality, and translation commutation are all
-- constructed.  There is no independent plus-block/endpoint receipt left to
-- disagree with x(c).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119LeastPrivilegeSourceRound152Exact as R152
import DASHI.Physics.YangMills.BalabanPeriodicSegmentCommutationRound162Exact as R162
import DASHI.Physics.YangMills.BalabanTranslatedCenteredEmbeddingRound163Exact as R163
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

    -- Only the c- block is selected independently.
    minusEmbedding :
      Nat → Embed.CenteredPeriodicNoWrapEmbedding n sourceRadius

    -- Literal coarse bond c: source axis and orientation only.
    coarseAxis : Nat → Contours.Axis4
    coarseDirection : Nat → Contours.Direction

open CanonicalL13Equation119Source public

coarseSegmentAt :
  ∀ {C n Value group} →
  CanonicalL13Equation119Source C n Value group →
  Nat → Contours.AxisSegment
coarseSegmentAt source step =
  canonicalCoarseSegment
    (coarseAxis source step) (coarseDirection source step)

-- The source c+ block is definitionally the coarse translate of c-.
derivedPlusEmbedding :
  ∀ {C n Value group} →
  CanonicalL13Equation119Source C n Value group →
  Nat → Embed.CenteredPeriodicNoWrapEmbedding n sourceRadius
derivedPlusEmbedding source step =
  R163.translatedEmbedding
    (minusEmbedding source step)
    (coarseSegmentAt source step)

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
  ; R152.LiteralEquation119LeastPrivilegeSource.plusEmbedding =
      derivedPlusEmbedding source
  ; R152.LiteralEquation119LeastPrivilegeSource.coarseSegment =
      coarseSegmentAt source
  ; R152.LiteralEquation119LeastPrivilegeSource.coarseSegmentEndsAtPlusCentre =
      λ step → refl
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

round152PlusEmbeddingIsCoarseTranslate :
  ∀ {C n Value group}
    (source : CanonicalL13Equation119Source C n Value group)
    step →
  R152.plusEmbedding (asRound152Source source) step
  ≡ R163.translatedEmbedding
      (minusEmbedding source step)
      (coarseSegmentAt source step)
round152PlusEmbeddingIsCoarseTranslate source step = refl

round152CentreEndpointIsConstructed :
  ∀ {C n Value group}
    (source : CanonicalL13Equation119Source C n Value group)
    step →
  Bond.walk
    (Embed.embeddingCentre (minusEmbedding source step))
    (Periodic.segmentWord (coarseSegmentAt source step))
  ≡ Embed.embeddingCentre
      (R152.plusEmbedding (asRound152Source source) step)
round152CentreEndpointIsConstructed source step = refl

round152TranslationCommutationIsDerived :
  ∀ {C n Value group}
    (source : CanonicalL13Equation119Source C n Value group) →
  R152.translationCommutation (asRound152Source source)
  ≡ R162.periodicSegmentCommutation n
round152TranslationCommutationIsDerived source = refl

cmp98Equation119CanonicalCoarseSegmentRound158Level : ProofLevel
cmp98Equation119CanonicalCoarseSegmentRound158Level = machineChecked

cmp98Equation119DerivedPlusEmbeddingRound158Level : ProofLevel
cmp98Equation119DerivedPlusEmbeddingRound158Level = machineChecked

cmp98Equation119DerivedTranslationCommutationRound158Level : ProofLevel
cmp98Equation119DerivedTranslationCommutationRound158Level = machineChecked

-- The entire translated-block geometry is now construction.  The remaining
-- source-facing coarse datum is only which coordinate axis/orientation is the
-- printed coarse bond c at each step.
literalCMP98CoarseAxisOrientationRound158Level : ProofLevel
literalCMP98CoarseAxisOrientationRound158Level = conditional
