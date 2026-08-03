module DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopConventionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- One immutable convention receipt for the literal one-loop calculation.
--
-- Kenneth G. Wilson, "Confinement of Quarks", Physical Review D 10 (1974),
-- 2445--2459. DOI: 10.1103/PhysRevD.10.2445.
--
-- Ludwig D. Faddeev and Victor N. Popov, "Feynman Diagrams for the Yang--Mills
-- Field", Physics Letters B 25 (1967), 29--30.
-- DOI: 10.1016/0370-2693(67)90067-6.
--
-- Luis F. Abbott, "The Background Field Method Beyond One Loop", Nuclear
-- Physics B 185 (1981), 189--203.
-- DOI: 10.1016/0550-3213(81)90371-0.
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I", Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
------------------------------------------------------------------------

data GeneratorConvention : Set where
  antiHermitianPauliHalf : GeneratorConvention

data FourierConvention : Set where
  unitaryFiniteTorusTransform : FourierConvention

data GaugeConvention : Set where
  backgroundFeynmanGauge : GaugeConvention

data HaarChartConvention : Set where
  exponentialQuaternionChart : HaarChartConvention

data BackgroundSplitConvention : Set where
  rightTrivializedBackgroundFluctuation : BackgroundSplitConvention

record WilsonOneLoopConvention : Set where
  field
    dimension : Nat
    generatorConvention : GeneratorConvention
    fourierConvention : FourierConvention
    gaugeConvention : GaugeConvention
    haarChartConvention : HaarChartConvention
    backgroundSplitConvention : BackgroundSplitConvention

    wilsonActionHasOneMinusHalfTrace : Bool
    latticeSpacingAbsorbedIntoMomentum : Bool
    hatMomentumUsesTwoSinHalf : Bool
    ghostSignIncludedInKernel : Bool
    haarQuadraticTermIncluded : Bool

open WilsonOneLoopConvention public

canonicalWilsonOneLoopConvention : WilsonOneLoopConvention
canonicalWilsonOneLoopConvention = record
  { dimension = 4
  ; generatorConvention = antiHermitianPauliHalf
  ; fourierConvention = unitaryFiniteTorusTransform
  ; gaugeConvention = backgroundFeynmanGauge
  ; haarChartConvention = exponentialQuaternionChart
  ; backgroundSplitConvention = rightTrivializedBackgroundFluctuation
  ; wilsonActionHasOneMinusHalfTrace = true
  ; latticeSpacingAbsorbedIntoMomentum = true
  ; hatMomentumUsesTwoSinHalf = true
  ; ghostSignIncludedInKernel = true
  ; haarQuadraticTermIncluded = true
  }

adjointCasimirSU2 betaNormalization universalColorCoefficient : ℚ
adjointCasimirSU2 = + 2 / 1
betaNormalization = + 1 / 8
universalColorCoefficient = + 11 / 24

universalColorCoefficientExact :
  (+ 11 / 3) * betaNormalization ≡ universalColorCoefficient
universalColorCoefficientExact = ℚRing.solve-∀
canonicalConventionLevel : ProofLevel
canonicalConventionLevel = machineChecked

universalCoefficientNormalizationLevel : ProofLevel
universalCoefficientNormalizationLevel = machineChecked
