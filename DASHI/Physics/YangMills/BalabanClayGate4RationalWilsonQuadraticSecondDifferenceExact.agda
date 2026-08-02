module DASHI.Physics.YangMills.BalabanClayGate4RationalWilsonQuadraticSecondDifferenceExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
import Relation.Binary.PropositionalEquality as Eq

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact local Wilson quadratic second variation in ambient quaternion
-- coordinates.
--
-- Kenneth G. Wilson, "Confinement of Quarks",
-- Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- The repository already proves that the SU(2) Wilson trace deficit is one
-- half of the squared chordal distance.  The theorem below computes the exact
-- central second difference of that quadratic ambient cost.  It supplies the
-- curvature-channel middle operator; transport and chart remainders arise only
-- when the plaquette map itself is differentiated.
------------------------------------------------------------------------

record RationalQuaternionVariation : Set where
  constructor rationalQuaternionVariation
  field
    realPart imagI imagJ imagK : ℚ

open RationalQuaternionVariation public

addVariation :
  RationalQuaternionVariation → RationalQuaternionVariation →
  RationalQuaternionVariation
addVariation left right = rationalQuaternionVariation
  (realPart left + realPart right)
  (imagI left + imagI right)
  (imagJ left + imagJ right)
  (imagK left + imagK right)

subtractVariation :
  RationalQuaternionVariation → RationalQuaternionVariation →
  RationalQuaternionVariation
subtractVariation left right = rationalQuaternionVariation
  (realPart left - realPart right)
  (imagI left - imagI right)
  (imagJ left - imagJ right)
  (imagK left - imagK right)

variationNormSq : RationalQuaternionVariation → ℚ
variationNormSq value =
  realPart value * realPart value
  + imagI value * imagI value
  + imagJ value * imagJ value
  + imagK value * imagK value

quadraticWilsonCost : ℚ → RationalQuaternionVariation → ℚ
quadraticWilsonCost coefficient value =
  coefficient * variationNormSq value

ambientParallelogramCoordinate :
  ∀ a b c d x y z w →
  ((a + x) * (a + x)
    + (b + y) * (b + y)
    + (c + z) * (c + z)
    + (d + w) * (d + w))
  + ((a - x) * (a - x)
    + (b - y) * (b - y)
    + (c - z) * (c - z)
    + (d - w) * (d - w))
  ≡
  ((a * a + b * b + c * c + d * d)
    + (a * a + b * b + c * c + d * d))
  + ((x * x + y * y + z * z + w * w)
    + (x * x + y * y + z * z + w * w))
ambientParallelogramCoordinate = ℚRing.solve-∀

ambientParallelogramIdentity : ∀ base variation →
  variationNormSq (addVariation base variation)
  + variationNormSq (subtractVariation base variation)
  ≡
  (variationNormSq base + variationNormSq base)
  + (variationNormSq variation + variationNormSq variation)
ambientParallelogramIdentity
  (rationalQuaternionVariation a b c d)
  (rationalQuaternionVariation x y z w) =
  ambientParallelogramCoordinate a b c d x y z w

quadraticCentralSecondDifferenceCoordinate :
  ∀ coefficient a b c d x y z w →
  coefficient *
    ((a + x) * (a + x)
      + (b + y) * (b + y)
      + (c + z) * (c + z)
      + (d + w) * (d + w))
  + coefficient *
    ((a - x) * (a - x)
      + (b - y) * (b - y)
      + (c - z) * (c - z)
      + (d - w) * (d - w))
  - (coefficient * (a * a + b * b + c * c + d * d)
    + coefficient * (a * a + b * b + c * c + d * d))
  ≡
  (coefficient + coefficient)
    * (x * x + y * y + z * z + w * w)
quadraticCentralSecondDifferenceCoordinate = ℚRing.solve-∀

quadraticWilsonCentralSecondDifference : ∀ coefficient base variation →
  quadraticWilsonCost coefficient (addVariation base variation)
  + quadraticWilsonCost coefficient (subtractVariation base variation)
  - (quadraticWilsonCost coefficient base
    + quadraticWilsonCost coefficient base)
  ≡
  (coefficient + coefficient) * variationNormSq variation
quadraticWilsonCentralSecondDifference coefficient
  (rationalQuaternionVariation a b c d)
  (rationalQuaternionVariation x y z w) =
  quadraticCentralSecondDifferenceCoordinate
    coefficient a b c d x y z w

quadraticWilsonSecondVariationIndependentOfBase :
  ∀ coefficient leftBase rightBase variation →
  quadraticWilsonCost coefficient (addVariation leftBase variation)
  + quadraticWilsonCost coefficient (subtractVariation leftBase variation)
  - (quadraticWilsonCost coefficient leftBase
    + quadraticWilsonCost coefficient leftBase)
  ≡
  quadraticWilsonCost coefficient (addVariation rightBase variation)
  + quadraticWilsonCost coefficient (subtractVariation rightBase variation)
  - (quadraticWilsonCost coefficient rightBase
    + quadraticWilsonCost coefficient rightBase)
quadraticWilsonSecondVariationIndependentOfBase coefficient leftBase rightBase variation =
  let leftExact = quadraticWilsonCentralSecondDifference
        coefficient leftBase variation
      rightExact = quadraticWilsonCentralSecondDifference
        coefficient rightBase variation
  in Eq.trans leftExact (Eq.sym rightExact)

wilsonAmbientParallelogramLevel : ProofLevel
wilsonAmbientParallelogramLevel = machineChecked

wilsonQuadraticSecondDifferenceLevel : ProofLevel
wilsonQuadraticSecondDifferenceLevel = machineChecked

physicalPlaquetteDerivativeChainRuleInputsLevel : ProofLevel
physicalPlaquetteDerivativeChainRuleInputsLevel = conditional
