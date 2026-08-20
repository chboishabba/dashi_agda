module DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeMobiusDegreeLayerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Gian-Carlo Rota,
-- "On the Foundations of Combinatorial Theory I. Theory of Möbius
-- Functions", Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte
-- Gebiete 2 (1964), 340--368. DOI: 10.1007/BF00531932.
--
-- DASHI CONTRIBUTION
--
-- Sum the Boolean-four-cube Möbius atoms by cardinality BEFORE numerical
-- enclosure.  If
--
--   F_j = sum_{|S|=j} F(S),
--
-- then direct finite normalization gives
--
--   A_1 = F_1 - 4 F_0
--   A_2 = F_2 - 3 F_1 + 6 F_0
--   A_3 = F_3 - 2 F_2 + 3 F_1 - 4 F_0
--   A_4 = F_4 - F_3 + F_2 - F_1 + F_0.
--
-- These are the exact binomial layer coefficients
-- (-1)^(d-j) C(4-j,d-j).  For the physical zero-background subset partials
-- F_0=0, the four grouped G2 raw/source/defect quantities therefore depend on
-- only the four nonempty cardinality-layer sums, with all internal Möbius
-- cancellation preserved algebraically.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeMobiusExact as Mobius

layer0 layer1 layer2 layer3 layer4 : (Cube.Subset4 → ℚ) → ℚ
layer0 value = value Cube.empty
layer1 value = Sums.sumRational Cube.singletonSubsets4 value
layer2 value = Sums.sumRational Cube.pairSubsets4 value
layer3 value = Sums.sumRational Cube.tripleSubsets4 value
layer4 value = Sums.sumRational Cube.quarticSubsets4 value

mobiusDegree1 mobiusDegree2 mobiusDegree3 mobiusDegree4 :
  (Cube.Subset4 → ℚ) → ℚ
mobiusDegree1 value =
  Sums.sumRational Cube.singletonSubsets4 (Mobius.mobiusAtom value)
mobiusDegree2 value =
  Sums.sumRational Cube.pairSubsets4 (Mobius.mobiusAtom value)
mobiusDegree3 value =
  Sums.sumRational Cube.tripleSubsets4 (Mobius.mobiusAtom value)
mobiusDegree4 value =
  Sums.sumRational Cube.quarticSubsets4 (Mobius.mobiusAtom value)

mobiusDegree1LayerFormula : ∀ value →
  mobiusDegree1 value
  ≡ layer1 value - (+ 4 / 1) * layer0 value
mobiusDegree1LayerFormula value =
  ℚRing.solve-∀
    (value Cube.empty)
    (value Cube.s0) (value Cube.s1) (value Cube.s2) (value Cube.s3)

mobiusDegree2LayerFormula : ∀ value →
  mobiusDegree2 value
  ≡ layer2 value
    - (+ 3 / 1) * layer1 value
    + (+ 6 / 1) * layer0 value
mobiusDegree2LayerFormula value =
  ℚRing.solve-∀
    (value Cube.empty)
    (value Cube.s0) (value Cube.s1) (value Cube.s2) (value Cube.s3)
    (value Cube.s01) (value Cube.s02) (value Cube.s03)
    (value Cube.s12) (value Cube.s13) (value Cube.s23)

mobiusDegree3LayerFormula : ∀ value →
  mobiusDegree3 value
  ≡ layer3 value
    - (+ 2 / 1) * layer2 value
    + (+ 3 / 1) * layer1 value
    - (+ 4 / 1) * layer0 value
mobiusDegree3LayerFormula value =
  ℚRing.solve-∀
    (value Cube.empty)
    (value Cube.s0) (value Cube.s1) (value Cube.s2) (value Cube.s3)
    (value Cube.s01) (value Cube.s02) (value Cube.s03)
    (value Cube.s12) (value Cube.s13) (value Cube.s23)
    (value Cube.s012) (value Cube.s013) (value Cube.s023) (value Cube.s123)

mobiusDegree4LayerFormula : ∀ value →
  mobiusDegree4 value
  ≡ layer4 value - layer3 value + layer2 value - layer1 value + layer0 value
mobiusDegree4LayerFormula value =
  ℚRing.solve-∀
    (value Cube.empty)
    (value Cube.s0) (value Cube.s1) (value Cube.s2) (value Cube.s3)
    (value Cube.s01) (value Cube.s02) (value Cube.s03)
    (value Cube.s12) (value Cube.s13) (value Cube.s23)
    (value Cube.s012) (value Cube.s013) (value Cube.s023) (value Cube.s123)
    (value Cube.s0123)

mobiusDegree1ZeroBackground : ∀ value → value Cube.empty ≡ 0ℚ →
  mobiusDegree1 value ≡ layer1 value
mobiusDegree1ZeroBackground value emptyZero =
  trans
    (mobiusDegree1LayerFormula value)
    (subst
      (λ background →
        layer1 value - (+ 4 / 1) * background ≡ layer1 value)
      (sym emptyZero)
      (ℚRing.solve-∀ (layer1 value)))

mobiusDegree2ZeroBackground : ∀ value → value Cube.empty ≡ 0ℚ →
  mobiusDegree2 value
  ≡ layer2 value - (+ 3 / 1) * layer1 value
mobiusDegree2ZeroBackground value emptyZero =
  trans
    (mobiusDegree2LayerFormula value)
    (subst
      (λ background →
        layer2 value - (+ 3 / 1) * layer1 value
          + (+ 6 / 1) * background
        ≡ layer2 value - (+ 3 / 1) * layer1 value)
      (sym emptyZero)
      (ℚRing.solve-∀ (layer1 value) (layer2 value)))

mobiusDegree3ZeroBackground : ∀ value → value Cube.empty ≡ 0ℚ →
  mobiusDegree3 value
  ≡ layer3 value
    - (+ 2 / 1) * layer2 value
    + (+ 3 / 1) * layer1 value
mobiusDegree3ZeroBackground value emptyZero =
  trans
    (mobiusDegree3LayerFormula value)
    (subst
      (λ background →
        layer3 value
          - (+ 2 / 1) * layer2 value
          + (+ 3 / 1) * layer1 value
          - (+ 4 / 1) * background
        ≡ layer3 value
          - (+ 2 / 1) * layer2 value
          + (+ 3 / 1) * layer1 value)
      (sym emptyZero)
      (ℚRing.solve-∀ (layer1 value) (layer2 value) (layer3 value)))

mobiusDegree4ZeroBackground : ∀ value → value Cube.empty ≡ 0ℚ →
  mobiusDegree4 value
  ≡ layer4 value - layer3 value + layer2 value - layer1 value
mobiusDegree4ZeroBackground value emptyZero =
  trans
    (mobiusDegree4LayerFormula value)
    (subst
      (λ background →
        layer4 value - layer3 value + layer2 value - layer1 value + background
        ≡ layer4 value - layer3 value + layer2 value - layer1 value)
      (sym emptyZero)
      (ℚRing.solve-∀
        (layer1 value) (layer2 value) (layer3 value) (layer4 value)))

booleanFourCubeMobiusDegreeLayerFormulaLevel : ProofLevel
booleanFourCubeMobiusDegreeLayerFormulaLevel = machineChecked

booleanFourCubeMobiusDegreeZeroBackgroundLevel : ProofLevel
booleanFourCubeMobiusDegreeZeroBackgroundLevel = machineChecked
