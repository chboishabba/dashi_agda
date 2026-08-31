{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveCoarseBondSourceRound182Exact where

------------------------------------------------------------------------
-- ROUND182 A1 BIDI: THE PRINTED COARSE BOND OWNS AXIS + ORIENTATION
--
-- Primary sources:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I", Commun. Math. Phys. 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Round158 still stored `coarseAxis` and `coarseDirection` independently.
-- But the physical repository carrier already represents a positive coarse bond
-- as `(site , axis)`.  Its orientation is positive by type and its axis is the
-- second projection.  Therefore the strongest source should store the actual
-- positive coarse bond and derive both Round158 fields.
--
-- The conversion below is only between the repository's kernel-visible
-- four-element axis carrier and the shortest-contour enumeration's four named
-- constructors.  It contains no physical choice.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Blocks
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Word
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158

carrierAxisToContourAxis : Carrier.Axis4 → Contours.Axis4
carrierAxisToContourAxis Carrier.zeroᵢ = Contours.axis0
carrierAxisToContourAxis (Carrier.sucᵢ Carrier.zeroᵢ) = Contours.axis1
carrierAxisToContourAxis (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ)) = Contours.axis2
carrierAxisToContourAxis
  (Carrier.sucᵢ (Carrier.sucᵢ (Carrier.sucᵢ Carrier.zeroᵢ))) = Contours.axis3

record PositiveCoarseBondEquation119Source
    (C : R146.SignedAdditiveOperatorCarrier)
    (n coarseSide : Nat)
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

    minusEmbedding :
      Nat → Embed.CenteredPeriodicNoWrapEmbedding n R158.sourceRadius

    -- The actual source coarse bond.  Positive orientation is in the type.
    coarseBond : Nat → Carrier.PositiveBond coarseSide

open PositiveCoarseBondEquation119Source public

coarseAxisFromBond :
  ∀ {C n coarseSide Value group} →
  PositiveCoarseBondEquation119Source C n coarseSide Value group →
  Nat → Contours.Axis4
coarseAxisFromBond source step =
  carrierAxisToContourAxis (Carrier.second (coarseBond source step))

coarseDirectionFromPositiveBond :
  ∀ {C n coarseSide Value group} →
  PositiveCoarseBondEquation119Source C n coarseSide Value group →
  Nat → Contours.Direction
coarseDirectionFromPositiveBond source step = Contours.positive

asCanonicalL13Equation119Source :
  ∀ {C n coarseSide Value group} →
  PositiveCoarseBondEquation119Source C n coarseSide Value group →
  R158.CanonicalL13Equation119Source C n Value group
asCanonicalL13Equation119Source source = record
  { R158.CanonicalL13Equation119Source.realization = realization source
  ; R158.CanonicalL13Equation119Source.bondComponent = bondComponent source
  ; R158.CanonicalL13Equation119Source.adjointLink = adjointLink source
  ; R158.CanonicalL13Equation119Source.scaleV = scaleV source
  ; R158.CanonicalL13Equation119Source.qSource = qSource source
  ; R158.CanonicalL13Equation119Source.minusEmbedding = minusEmbedding source
  ; R158.CanonicalL13Equation119Source.coarseAxis = coarseAxisFromBond source
  ; R158.CanonicalL13Equation119Source.coarseDirection =
      coarseDirectionFromPositiveBond source
  }

canonicalAxisIsPositiveBondAxis :
  ∀ {C n coarseSide Value group}
    (source : PositiveCoarseBondEquation119Source
      C n coarseSide Value group) step →
  R158.coarseAxis (asCanonicalL13Equation119Source source) step
  ≡ carrierAxisToContourAxis (Carrier.second (coarseBond source step))
canonicalAxisIsPositiveBondAxis source step = Agda.Builtin.Equality.refl

canonicalDirectionIsPositive :
  ∀ {C n coarseSide Value group}
    (source : PositiveCoarseBondEquation119Source
      C n coarseSide Value group) step →
  R158.coarseDirection (asCanonicalL13Equation119Source source) step
  ≡ Contours.positive
canonicalDirectionIsPositive source step = Agda.Builtin.Equality.refl

canonicalCoarseSegmentIsPositiveBondAxisL13 :
  ∀ {C n coarseSide Value group}
    (source : PositiveCoarseBondEquation119Source
      C n coarseSide Value group) step →
  R158.coarseSegmentAt (asCanonicalL13Equation119Source source) step
  ≡ R158.canonicalCoarseSegment
      (carrierAxisToContourAxis (Carrier.second (coarseBond source step)))
      Contours.positive
canonicalCoarseSegmentIsPositiveBondAxisL13 source step =
  Agda.Builtin.Equality.refl

cmp98Equation119PositiveCoarseBondSourceRound182Level : ProofLevel
cmp98Equation119PositiveCoarseBondSourceRound182Level = machineChecked

cmp98Equation119CoarseAxisOrientationDerivedRound182Level : ProofLevel
cmp98Equation119CoarseAxisOrientationDerivedRound182Level = machineChecked

-- The printed coarse-bond axis/orientation is no longer an independent source
-- seam on this path.  What remains is same-object realization of this positive
-- coarse bond and the existing dyadic physical transported-relative product.
literalCMP98PositiveCoarseBondSameObjectRound182Level : ProofLevel
literalCMP98PositiveCoarseBondSameObjectRound182Level = conditional
