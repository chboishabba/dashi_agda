module DASHI.Physics.YangMills.BalabanClayGate4DyadicGeometricRootedSummabilityExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact dyadic rooted-polymer summability.
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- Once entropy times decay is at most 1/2, every rooted shell sum is controlled
-- by a dyadic geometric series.  Rather than assuming a bound for every partial
-- sum, we prove the exact finite identity
--
--   sum_{m < n} g 2^{-m} + 2 g 2^{-n} = 2 g.
--
-- The order consequence then needs only nonnegativity of the explicit tail.
------------------------------------------------------------------------

halfℚ : ℚ
halfℚ = + 1 / 2

dyadicPower : Nat → ℚ
dyadicPower zero = 1ℚ
dyadicPower (suc exponent) = halfℚ * dyadicPower exponent

dyadicRootedPartial : ℚ → Nat → ℚ
dyadicRootedPartial amplitude zero = 0ℚ
dyadicRootedPartial amplitude (suc depth) =
  amplitude * dyadicPower depth
  + dyadicRootedPartial amplitude depth

dyadicTail : ℚ → Nat → ℚ
dyadicTail amplitude depth =
  (amplitude + amplitude) * dyadicPower depth

dyadicStepRegroup : ∀ amplitude partial power →
  amplitude * power + partial
  + (amplitude + amplitude) * (halfℚ * power)
  ≡ partial + (amplitude + amplitude) * power
dyadicStepRegroup = ℚRing.solve-∀

dyadicRootedZeroExact : ∀ amplitude →
  0ℚ + (amplitude + amplitude) * 1ℚ ≡ amplitude + amplitude
dyadicRootedZeroExact = ℚRing.solve-∀

dyadicRootedPartialPlusTailExact : ∀ amplitude depth →
  dyadicRootedPartial amplitude depth + dyadicTail amplitude depth
  ≡ amplitude + amplitude
dyadicRootedPartialPlusTailExact amplitude zero =
  dyadicRootedZeroExact amplitude

dyadicRootedPartialPlusTailExact amplitude (suc depth) =
  trans
    (dyadicStepRegroup amplitude
      (dyadicRootedPartial amplitude depth)
      (dyadicPower depth))
    (dyadicRootedPartialPlusTailExact amplitude depth)

record DyadicTailOrder : Set₁ where
  field
    LessEqual : ℚ → ℚ → Set
    tailNonnegative : ∀ amplitude depth →
      LessEqual 0ℚ (dyadicTail amplitude depth)
    leftBelowTotalFromNonnegativeTail : ∀ left tail total →
      left + tail ≡ total →
      LessEqual 0ℚ tail →
      LessEqual left total

open DyadicTailOrder public

dyadicRootedPartialBelowDoubleAmplitude :
  (order : DyadicTailOrder) →
  ∀ amplitude depth →
  LessEqual order
    (dyadicRootedPartial amplitude depth)
    (amplitude + amplitude)
dyadicRootedPartialBelowDoubleAmplitude order amplitude depth =
  leftBelowTotalFromNonnegativeTail order
    (dyadicRootedPartial amplitude depth)
    (dyadicTail amplitude depth)
    (amplitude + amplitude)
    (dyadicRootedPartialPlusTailExact amplitude depth)
    (tailNonnegative order amplitude depth)

dyadicRootedExactTailIdentityLevel : ProofLevel
dyadicRootedExactTailIdentityLevel = machineChecked

dyadicRootedOrderClosureLevel : ProofLevel
dyadicRootedOrderClosureLevel = machineChecked

physicalDyadicTailNonnegativityInputsLevel : ProofLevel
physicalDyadicTailNonnegativityInputsLevel = conditional
