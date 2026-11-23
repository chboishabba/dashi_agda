module DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusExact where

------------------------------------------------------------------------
-- BISHOP UPPER-HALF-PLANE q-RADIUS
--
-- DASHI CONTRIBUTION
--
-- For any positive Bishop real pi-candidate and positive imaginary coordinate,
--
--   r = exp(-(2*pi*Im tau))
--
-- lies strictly between zero and one.  This is the exact scalar radius needed
-- by the already-owned polynomial/geometric E4/E6 majorant theorem.
--
-- The specialization to bishopMachinPi is concrete.  It is NOT a claim that
-- bishopMachinPi has already been identified with the legacy/trigonometric pi
-- occurring in the older ConcreteComplex q evaluator.  That same-object weld
-- remains separate and fail-closed.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (0ℚᵘ; _/_)
import Data.Rational.Unnormalised.Properties as RatP

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Foundations.BishopSqrtTwoThirdsMachinConstantExact as MachinPositive
import DASHI.Foundations.BishopNegativeExponentialGlobalUnitIntervalExact as NegExp
import DASHI.Moonshine.JInvariantEisensteinBishopMajorantSeriesExact as Majorant

two : BishopReal.ℝ
two = Exp.embed (+ 2 / 1)

twoPositive : BishopReal._<_ BishopReal.0ℝ two
twoPositive =
  BishopP.p<q⇒p⋆<q⋆
    0ℚᵘ (+ 2 / 1)
    (RatP.positive⁻¹ (+ 2 / 1))

qExponentMagnitude :
  BishopReal.ℝ →
  BishopReal.ℝ →
  BishopReal.ℝ
qExponentMagnitude piB imag =
  BishopReal._*_
    (BishopReal._*_ two piB)
    imag

qExponentMagnitudePositive :
  ∀ {piB imag : BishopReal.ℝ} →
  BishopReal._<_ BishopReal.0ℝ piB →
  BishopReal._<_ BishopReal.0ℝ imag →
  BishopReal._<_ BishopReal.0ℝ (qExponentMagnitude piB imag)
qExponentMagnitudePositive piPositive imagPositive =
  BishopP.posx⇒0<x
    (BishopP.posx,y⇒posx*y
      (BishopP.posx,y⇒posx*y
        (BishopP.0<x⇒posx twoPositive)
        (BishopP.0<x⇒posx piPositive))
      (BishopP.0<x⇒posx imagPositive))

qRadius :
  BishopReal.ℝ →
  BishopReal.ℝ →
  BishopReal.ℝ
qRadius piB imag =
  Exp.bishopExp
    (BishopReal.- (qExponentMagnitude piB imag))

qRadiusPositive :
  ∀ {piB imag : BishopReal.ℝ} →
  BishopReal._<_ BishopReal.0ℝ piB →
  BishopReal._<_ BishopReal.0ℝ imag →
  BishopReal._<_ BishopReal.0ℝ (qRadius piB imag)
qRadiusPositive piPositive imagPositive =
  NegExp.negativeExpPositive
    (qExponentMagnitudePositive piPositive imagPositive)

qRadiusBelowOne :
  ∀ {piB imag : BishopReal.ℝ} →
  BishopReal._<_ BishopReal.0ℝ piB →
  BishopReal._<_ BishopReal.0ℝ imag →
  BishopReal._<_ (qRadius piB imag) BishopReal.1ℝ
qRadiusBelowOne piPositive imagPositive =
  NegExp.negativeExpBelowOne
    (qExponentMagnitudePositive piPositive imagPositive)

qRadiusUnitInterval :
  ∀ {piB imag : BishopReal.ℝ} →
  BishopReal._<_ BishopReal.0ℝ piB →
  BishopReal._<_ BishopReal.0ℝ imag →
  Unit.BishopUnitIntervalRatio (qRadius piB imag)
qRadiusUnitInterval piPositive imagPositive = record
  { Unit.ratioNonnegative =
      BishopP.<⇒≤ (qRadiusPositive piPositive imagPositive)
  ; Unit.ratioBelowOne =
      qRadiusBelowOne piPositive imagPositive
  }

machinQRadius : BishopReal.ℝ → BishopReal.ℝ
machinQRadius =
  qRadius Machin.bishopMachinPi

machinQRadiusUnitInterval :
  ∀ {imag : BishopReal.ℝ} →
  BishopReal._<_ BishopReal.0ℝ imag →
  Unit.BishopUnitIntervalRatio (machinQRadius imag)
machinQRadiusUnitInterval imagPositive =
  qRadiusUnitInterval
    MachinPositive.machinPiPositive
    imagPositive


------------------------------------------------------------------------
-- Direct Eisenstein majorant receipts from positive Bishop upper-half-plane
-- data.  This stays entirely on the Bishop carrier.
------------------------------------------------------------------------

e4MajorantAbsoluteConvergenceAtUpperHalfPlane :
  ∀ {piB imag : BishopReal.ℝ} →
  (piPositive : BishopReal._<_ BishopReal.0ℝ piB) →
  (imagPositive : BishopReal._<_ BishopReal.0ℝ imag) →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (Majorant.e4MajorantTerm (qRadius piB imag))
e4MajorantAbsoluteConvergenceAtUpperHalfPlane
    piPositive imagPositive =
  Majorant.e4MajorantAbsoluteConvergence
    (qRadiusUnitInterval piPositive imagPositive)

e6MajorantAbsoluteConvergenceAtUpperHalfPlane :
  ∀ {piB imag : BishopReal.ℝ} →
  (piPositive : BishopReal._<_ BishopReal.0ℝ piB) →
  (imagPositive : BishopReal._<_ BishopReal.0ℝ imag) →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (Majorant.e6MajorantTerm (qRadius piB imag))
e6MajorantAbsoluteConvergenceAtUpperHalfPlane
    piPositive imagPositive =
  Majorant.e6MajorantAbsoluteConvergence
    (qRadiusUnitInterval piPositive imagPositive)

machinE4MajorantAbsoluteConvergence :
  ∀ {imag : BishopReal.ℝ} →
  BishopReal._<_ BishopReal.0ℝ imag →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (Majorant.e4MajorantTerm (machinQRadius imag))
machinE4MajorantAbsoluteConvergence imagPositive =
  Majorant.e4MajorantAbsoluteConvergence
    (machinQRadiusUnitInterval imagPositive)

machinE6MajorantAbsoluteConvergence :
  ∀ {imag : BishopReal.ℝ} →
  BishopReal._<_ BishopReal.0ℝ imag →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (Majorant.e6MajorantTerm (machinQRadius imag))
machinE6MajorantAbsoluteConvergence imagPositive =
  Majorant.e6MajorantAbsoluteConvergence
    (machinQRadiusUnitInterval imagPositive)
