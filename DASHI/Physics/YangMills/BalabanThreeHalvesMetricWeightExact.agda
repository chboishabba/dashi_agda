{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanThreeHalvesMetricWeightExact where

------------------------------------------------------------------------
-- ROW C SPATIAL WEIGHT: METRIC TRIANGLE -> SUBMULTIPLICATIVE (3/2)^d
--
-- The existing CMP116 Hessian compiler uses the exponential lattice weight
--
--                     w(d) = (3/2)^d.
--
-- The weighted influence-power theorem asks that w>=1 and
--
--                 w(d(x,z)) <= w(d(x,y)) w(d(y,z)).
--
-- These are not Yang--Mills inputs.  They follow from exact rational power
-- algebra and the ordinary triangle inequality for the chosen integer distance.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Nat.Base as ℕ
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)
open import Relation.Nullary.Decidable using (toWitness)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanRootedKPToExponentialWeightedHessianExact as Hess
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

baseAtLeastOne : 1ℚ ≤ Hess.threeHalves
baseAtLeastOne = toWitness {a? = 1ℚ ℚP.≤? Hess.threeHalves} _

powerAtLeastOne : ∀ n → 1ℚ ≤ Hess.threeHalvesPower n
powerAtLeastOne zero = ℚP.≤-refl
powerAtLeastOne (suc n) =
  let
    previous = powerAtLeastOne n
    baseNN : 0ℚ ≤ Hess.threeHalves
    baseNN = Hess.threeHalvesNonnegative
    scaled = Norm.scaleʳ-nonNeg baseNN previous
  in
  ℚP.≤-trans baseAtLeastOne
    (subst
      (λ right → Hess.threeHalves ≤ right)
      (ℚP.*-identityˡ Hess.threeHalves)
      scaled)

powerMonotone : ∀ {m n} → m ℕ.≤ n →
  Hess.threeHalvesPower m ≤ Hess.threeHalvesPower n
powerMonotone {zero} {n} proof = powerAtLeastOne n
powerMonotone {suc m} {suc n} (ℕ.s≤s proof) =
  Norm.scaleʳ-nonNeg
    Hess.threeHalvesNonnegative
    (powerMonotone proof)

powerAdd : ∀ m n →
  Hess.threeHalvesPower (m ℕ.+ n)
  ≡ Hess.threeHalvesPower m * Hess.threeHalvesPower n
powerAdd zero n = sym (ℚP.*-identityˡ (Hess.threeHalvesPower n))
powerAdd (suc m) n
  rewrite powerAdd m n =
  ℚRing.solve-∀
    (Hess.threeHalvesPower m)
    (Hess.threeHalvesPower n)
    Hess.threeHalves

record NatMetricTriangle (Site : Set) : Set₁ where
  field
    distance : Site → Site → Nat
    triangle : ∀ x middle y →
      distance x y ℕ.≤ distance x middle ℕ.+ distance middle y

open NatMetricTriangle public

metricWeight : ∀ {Site} → NatMetricTriangle Site → Site → Site → ℚ
metricWeight metric x y = Hess.threeHalvesPower (distance metric x y)

metricWeightNonnegative :
  ∀ {Site} (metric : NatMetricTriangle Site) x y →
  0ℚ ≤ metricWeight metric x y
metricWeightNonnegative metric x y =
  Hess.threeHalvesPowerNonnegative (distance metric x y)

metricWeightAtLeastOne :
  ∀ {Site} (metric : NatMetricTriangle Site) x y →
  1ℚ ≤ metricWeight metric x y
metricWeightAtLeastOne metric x y = powerAtLeastOne (distance metric x y)

metricWeightTriangle :
  ∀ {Site} (metric : NatMetricTriangle Site) x middle y →
  metricWeight metric x y
  ≤ metricWeight metric x middle * metricWeight metric middle y
metricWeightTriangle metric x middle y =
  let
    monotone = powerMonotone (triangle metric x middle y)
  in
  subst
    (λ right → metricWeight metric x y ≤ right)
    (powerAdd (distance metric x middle) (distance metric middle y))
    monotone

threeHalvesPowerMonotoneLevel : ProofLevel
threeHalvesPowerMonotoneLevel = machineChecked

threeHalvesMetricWeightSubmultiplicativeLevel : ProofLevel
threeHalvesMetricWeightSubmultiplicativeLevel = machineChecked

-- The only physical choice left is the actual integer lattice/block distance
-- used by the same CMP116 Hessian mark; its triangle law is a property of that
-- carrier, not an analytic estimate.
literalYMSpatialDistanceIdentificationLevel : ProofLevel
literalYMSpatialDistanceIdentificationLevel = conditional
