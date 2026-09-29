module DASHI.Moonshine.OggSSPP2F4CurveKleinResidualSourceNoGoExact where

------------------------------------------------------------------------
-- A SOURCE-ARITHMETIC P2 CANDIDATE IS ELIMINATED BY COMPONENT COUNT
--
-- On the actual nine Banerjee special-fibre F4 points, Frobenius and
-- Weierstrass coordinate negation commute.  Their joint action has four
-- proven, reachable orbits (sizes 1,2,2,4).
--
-- Thus this ACTUAL curve-point action groupoid cannot itself be the
-- ten-component exceptional Monster-exponent residual source.
-- A separate genuinely marked / inertia-enriched arithmetic object is
-- still required.
--
-- Provenance: curve arithmetic/coordinates and attributed Monster
-- exponent are consumed independently; the no-go comparison is DASHI.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Moonshine.OggSSPP2F4CurveFrobeniusNegationOrbitExact as Klein
import DASHI.Moonshine.OggSSPMonstrousExponent369GluingExact as Exponent
import DASHI.Moonshine.OggSSPArithmeticResidualGroupoidRecognitionFunctorExact as Recognition

curveKleinOrbitCountIsFour : Klein.kleinOrbitCount ≡ 4
curveKleinOrbitCountIsFour = refl

arithmeticMonsterP2ResidualIsTen : Exponent.p2ExceptionalResidual ≡ 10
arithmeticMonsterP2ResidualIsTen = refl

curveKleinOrbitCountIsNotMonsterP2Residual :
  Klein.kleinOrbitCount ≡ Exponent.p2ExceptionalResidual → ⊥
curveKleinOrbitCountIsNotMonsterP2Residual ()

curveKleinCannotPassP2Pi0RecognitionGate :
  Recognition.Pi0RecognitionGate
    Exponent.p2ExceptionalResidual
    Klein.kleinOrbitCount
  → ⊥
curveKleinCannotPassP2Pi0RecognitionGate ()

record F4CurveKleinResidualSourceNoGoBoundary : Set where
  constructor f4-curve-klein-residual-source-no-go-boundary
  field
    geometricCurveKleinOrbitsActual : Bool
    fourOrbitsProvedByRepresentativesAndTransporters : Bool
    exceptionalP2ResidualTenIndependent : Bool
    fourOrbitSourcePassesTenOrbitRecognitionGate : Bool
    finiteFlatMarkedArithmeticSourceConstructed : Bool

canonicalF4CurveKleinResidualSourceNoGoBoundary :
  F4CurveKleinResidualSourceNoGoBoundary
canonicalF4CurveKleinResidualSourceNoGoBoundary =
  f4-curve-klein-residual-source-no-go-boundary
    true true true false false
