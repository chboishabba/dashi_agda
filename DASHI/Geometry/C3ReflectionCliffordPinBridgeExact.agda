module DASHI.Geometry.C3ReflectionCliffordPinBridgeExact where

-- Literal reflection on the signed ternary spatial chart, with the
-- Clifford-generator receipt for its Pin lift. This does not conflate
-- the spatial reflection with an SU(2) proper rotation.
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Algebra.BalancedTernary as T
import DASHI.Algebra.Clifford.ConcreteCl31Basis as Cl
import DASHI.Foundations.C3NineSiteBalancedChartExact as Chart
import DASHI.Foundations.C3NineSiteSixStepMirrorExact as Mirror
import DASHI.Foundations.C3NineSiteAlternatingOrbitExact as Orbit

negX : T.Trit → T.Trit
negX = T.negate

pinMirrorChart : Chart.ChartPoint → Chart.ChartPoint
pinMirrorChart (Chart.point row column) =
  Chart.point row (negX column)

pinMirrorInvolutive : ∀ p → pinMirrorChart (pinMirrorChart p) ≡ p
pinMirrorInvolutive (Chart.point T.neg T.neg) = refl
pinMirrorInvolutive (Chart.point T.neg T.zero) = refl
pinMirrorInvolutive (Chart.point T.neg T.pos) = refl
pinMirrorInvolutive (Chart.point T.zero T.neg) = refl
pinMirrorInvolutive (Chart.point T.zero T.zero) = refl
pinMirrorInvolutive (Chart.point T.zero T.pos) = refl
pinMirrorInvolutive (Chart.point T.pos T.neg) = refl
pinMirrorInvolutive (Chart.point T.pos T.zero) = refl
pinMirrorInvolutive (Chart.point T.pos T.pos) = refl

mirrorEncoding : ∀ s →
  Chart.encode (Mirror.mirror s) ≡ pinMirrorChart (Chart.encode s)
mirrorEncoding Orbit.TL = refl
mirrorEncoding Orbit.TM = refl
mirrorEncoding Orbit.TR = refl
mirrorEncoding Orbit.ML = refl
mirrorEncoding Orbit.MM = refl
mirrorEncoding Orbit.MR = refl
mirrorEncoding Orbit.BL = refl
mirrorEncoding Orbit.BM = refl
mirrorEncoding Orbit.BR = refl

-- In Cl(3,1), spatial e1 satisfies e1²=+1, and e1 anticommutes
-- with e0,e2,e3. The Pin twisted adjoint is rho_e1(v)=-e1 v e1.
-- Therefore it reverses e1 and fixes the other generators.
pinGenerator : Cl.Generator
pinGenerator = Cl.e1

pinGeneratorSquaresToOne :
  Cl.genMul pinGenerator (Cl.bladeOf pinGenerator) ≡
    (Cl.plus , Cl.one)
pinGeneratorSquaresToOne = refl

pinGeneratorAnticommutesWithE0 :
  Cl.genMul Cl.e1 (Cl.bladeOf Cl.e0)
    ≡ Cl.negSigned (Cl.genMul Cl.e0 (Cl.bladeOf Cl.e1))
pinGeneratorAnticommutesWithE0 = Cl.generatorAnticommutes Cl.a10

pinGeneratorAnticommutesWithE2 :
  Cl.genMul Cl.e1 (Cl.bladeOf Cl.e2)
    ≡ Cl.negSigned (Cl.genMul Cl.e2 (Cl.bladeOf Cl.e1))
pinGeneratorAnticommutesWithE2 = Cl.generatorAnticommutes Cl.a12

pinGeneratorAnticommutesWithE3 :
  Cl.genMul Cl.e1 (Cl.bladeOf Cl.e3)
    ≡ Cl.negSigned (Cl.genMul Cl.e3 (Cl.bladeOf Cl.e1))
pinGeneratorAnticommutesWithE3 = Cl.generatorAnticommutes Cl.a13

-- The full twisted-adjoint formula requires the actual associative
-- multivector product; ConcreteCl31Basis explicitly leaves this as a
-- separate linear extension. This bridge proves the underlying chart
-- action and supplies the exact generator-level Clifford ingredients.
