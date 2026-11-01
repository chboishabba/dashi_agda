module DASHI.Physics.Closure.NSTriadKNWienerL4ScalingNoGoRound108Exact where

------------------------------------------------------------------------
-- ROUND108 / WIENER-L4 SCALING NO-GO
--
-- Round107 reduced the positive Waleffe network-forcing budget to the
-- scale-critical expenditure
--
--   integral A(t)^2 L2(t) H1(t) dt,
--
-- where, under the 3D Navier--Stokes scaling
--
--   u_lambda(x,t) = lambda u(lambda x, lambda^2 t),
--
-- the scale degrees are
--
--   deg A   =  1,
--   deg L2  = -1/2,
--   deg H1  =  1/2,
--   deg dt  = -2.
--
-- Therefore A^2 L2 H1 has pointwise degree 2 and its time integral has
-- degree 0: it is critical.
--
-- A tempting Young reduction is
--
--   A^2 L2 H1 <= 1/2 A^4 L2^2 + 1/2 H1^2.
--
-- This file records the exact scaling obstruction.  The first Young term has
-- pointwise degree 3 and integrated degree 1.  Replacing L2^2 by an energy
-- ceiling leaves the still stronger integral A^4 dt, whose degree is 2.
-- Hence the L4_t Wiener shortcut is not a scale-preserving reformulation of
-- the Round107 critical wall.
--
-- This is route pruning, not a Navier--Stokes regularity theorem.  The live
-- route should instead preserve the resonant/shell geometry and improve the
-- discrete-Young step before two global l1 norms are paid.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([])
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

one two four half : ℚ
one  = Int.+ 1 / 1
two  = Int.+ 2 / 1
four = Int.+ 4 / 1
half = Int.+ 1 / 2

wienerADegree l2Degree h1Degree timeDegree : ℚ
wienerADegree = one
l2Degree = - half
h1Degree = half
timeDegree = - two

criticalPointwiseDegree : ℚ
criticalPointwiseDegree =
  two * wienerADegree + l2Degree + h1Degree

criticalIntegratedDegree : ℚ
criticalIntegratedDegree = criticalPointwiseDegree + timeDegree

youngA4L2SqPointwiseDegree : ℚ
youngA4L2SqPointwiseDegree =
  four * wienerADegree + two * l2Degree

youngA4L2SqIntegratedDegree : ℚ
youngA4L2SqIntegratedDegree =
  youngA4L2SqPointwiseDegree + timeDegree

wienerA4IntegratedDegree : ℚ
wienerA4IntegratedDegree = four * wienerADegree + timeDegree

criticalPointwiseDegreeIsTwo : criticalPointwiseDegree ≡ two
criticalPointwiseDegreeIsTwo = solve []

criticalIntegratedDegreeIsZero : criticalIntegratedDegree ≡ 0ℚ
criticalIntegratedDegreeIsZero = solve []

youngA4L2SqPointwiseDegreeIsThree :
  youngA4L2SqPointwiseDegree ≡ Int.+ 3 / 1
youngA4L2SqPointwiseDegreeIsThree = solve []

youngA4L2SqIntegratedDegreeIsOne :
  youngA4L2SqIntegratedDegree ≡ one
youngA4L2SqIntegratedDegreeIsOne = solve []

wienerA4IntegratedDegreeIsTwo : wienerA4IntegratedDegree ≡ two
wienerA4IntegratedDegreeIsTwo = solve []

------------------------------------------------------------------------
-- Frontier status.
------------------------------------------------------------------------

round108Round107SerrinWienerIntegralScaleCritical : Bool
round108Round107SerrinWienerIntegralScaleCritical = true

round108WienerL4ShortcutScaleCritical : Bool
round108WienerL4ShortcutScaleCritical = false

round108A4L2SqYoungTermScaleCritical : Bool
round108A4L2SqYoungTermScaleCritical = false

round108PreserveResonantShellGeometryBeforeGlobalL1 : Bool
round108PreserveResonantShellGeometryBeforeGlobalL1 = true

round108Round107SerrinWienerIntegralScaleCriticalIsTrue :
  round108Round107SerrinWienerIntegralScaleCritical ≡ true
round108Round107SerrinWienerIntegralScaleCriticalIsTrue = refl

round108WienerL4ShortcutScaleCriticalIsFalse :
  round108WienerL4ShortcutScaleCritical ≡ false
round108WienerL4ShortcutScaleCriticalIsFalse = refl

round108A4L2SqYoungTermScaleCriticalIsFalse :
  round108A4L2SqYoungTermScaleCritical ≡ false
round108A4L2SqYoungTermScaleCriticalIsFalse = refl

round108PreserveResonantShellGeometryBeforeGlobalL1IsTrue :
  round108PreserveResonantShellGeometryBeforeGlobalL1 ≡ true
round108PreserveResonantShellGeometryBeforeGlobalL1IsTrue = refl
