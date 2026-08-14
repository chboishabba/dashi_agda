module DASHI.Biology.Physical.C3CubeCyclotomicParsevalExact where

------------------------------------------------------------------------
-- Exact Parseval/Plancherel closure for the unnormalised C3^3 DFT.
-- The transform convention in C3CubeCyclotomicFourierExact has no forward
-- 1/27 factor, so spectral energy is exactly 27 times state-space energy.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; normalize)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

import DASHI.Biology.Physical.C3CubeCyclotomicFourierExact as F

normC : F.Cyclotomic3 → ℚ
normC z = F.realPart (z F.*C F.conjC z)

energy1 : F.Triple F.Cyclotomic3 → ℚ
energy1 (F.triple a b c) = normC a + normC b + normC c

oneDimensionalParsevalUnnormalised : (f : F.Triple F.Cyclotomic3) →
  energy1 (F.forward1 f) ≡ 3 * energy1 f
oneDimensionalParsevalUnnormalised
  (F.triple (F.cyc a0 a1) (F.cyc b0 b1) (F.cyc c0 c1)) = solve-∀

energy2 : F.Triple (F.Triple F.Cyclotomic3) → ℚ
energy2 (F.triple a b c) = energy1 a + energy1 b + energy1 c

energy3 : F.CubeSignal → ℚ
energy3 (F.triple a b c) = energy2 a + energy2 b + energy2 c

transposePreservesEnergy : (m : F.Triple (F.Triple F.Cyclotomic3)) →
  energy2 (F.transpose2 m) ≡ energy2 m
transposePreservesEnergy
  (F.triple
    (F.triple (F.cyc a0 a1) (F.cyc b0 b1) (F.cyc c0 c1))
    (F.triple (F.cyc d0 d1) (F.cyc e0 e1) (F.cyc f0 f1))
    (F.triple (F.cyc g0 g1) (F.cyc h0 h1) (F.cyc i0 i1))) = solve-∀

mapRowsForwardMultipliesEnergyBy3 :
  (m : F.Triple (F.Triple F.Cyclotomic3)) →
  energy2 (F.mapTriple F.forward1 m) ≡ 3 * energy2 m
mapRowsForwardMultipliesEnergyBy3 (F.triple a b c)
  rewrite oneDimensionalParsevalUnnormalised a
        | oneDimensionalParsevalUnnormalised b
        | oneDimensionalParsevalUnnormalised c = solve-∀

transformMatrixYMultipliesEnergyBy3 :
  (m : F.Triple (F.Triple F.Cyclotomic3)) →
  energy2 (F.transformMatrixY m) ≡ 3 * energy2 m
transformMatrixYMultipliesEnergyBy3 m
  rewrite transposePreservesEnergy (F.mapTriple F.forward1 (F.transpose2 m))
        | mapRowsForwardMultipliesEnergyBy3 (F.transpose2 m)
        | transposePreservesEnergy m = solve-∀

transformZMultipliesEnergyBy3 : (x : F.CubeSignal) →
  energy3 (F.transformZ x) ≡ 3 * energy3 x
transformZMultipliesEnergyBy3 (F.triple a b c)
  rewrite mapRowsForwardMultipliesEnergyBy3 a
        | mapRowsForwardMultipliesEnergyBy3 b
        | mapRowsForwardMultipliesEnergyBy3 c = solve-∀

transformYMultipliesEnergyBy3 : (x : F.CubeSignal) →
  energy3 (F.transformY x) ≡ 3 * energy3 x
transformYMultipliesEnergyBy3 (F.triple a b c)
  rewrite transformMatrixYMultipliesEnergyBy3 a
        | transformMatrixYMultipliesEnergyBy3 b
        | transformMatrixYMultipliesEnergyBy3 c = solve-∀

swapXYPreservesEnergy : (x : F.CubeSignal) →
  energy3 (F.swapXY x) ≡ energy3 x
swapXYPreservesEnergy
  (F.triple
    (F.triple a00 a01 a02)
    (F.triple a10 a11 a12)
    (F.triple a20 a21 a22))
  rewrite transposePreservesEnergy (F.triple a00 a10 a20)
        | transposePreservesEnergy (F.triple a01 a11 a21)
        | transposePreservesEnergy (F.triple a02 a12 a22) = solve-∀

transformXMultipliesEnergyBy3 : (x : F.CubeSignal) →
  energy3 (F.transformX x) ≡ 3 * energy3 x
transformXMultipliesEnergyBy3 x
  rewrite swapXYPreservesEnergy (F.transformY (F.swapXY x))
        | transformYMultipliesEnergyBy3 (F.swapXY x)
        | swapXYPreservesEnergy x = solve-∀

cubeParsevalUnnormalised : (f : F.CubeSignal) →
  energy3 (F.fourier27 f) ≡ 27 * energy3 f
cubeParsevalUnnormalised f
  rewrite transformXMultipliesEnergyBy3 (F.transformY (F.transformZ f))
        | transformYMultipliesEnergyBy3 (F.transformZ f)
        | transformZMultipliesEnergyBy3 f = solve-∀

twentySeventh : ℚ
twentySeventh = normalize 1 27

cubeParsevalNormalised : (f : F.CubeSignal) →
  twentySeventh * energy3 (F.fourier27 f) ≡ energy3 f
cubeParsevalNormalised f
  rewrite cubeParsevalUnnormalised f = solve-∀
