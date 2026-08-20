module DASHI.Physics.Closure.NSTriadKNC4aB2SurplusVelocityWorkSignNoGoRound87Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Dhawal Buaria; Alain Pumir.
-- Title: "Role of pressure in the dynamics of intense velocity gradients in
-- turbulent flows".
-- Journal of Fluid Mechanics 973 (2023), A23.
-- DOI: 10.1017/jfm.2023.786.
--
-- Authors: Koji Ohkitani; Shigeo Kishiba.
-- Title: "Nonlocal nature of vortex stretching in an inviscid fluid".
-- Physics of Fluids 7 (1995), 411--421.
-- DOI: 10.1063/1.868633.
--
-- ROUND87 / DECISIVE C4a SIGN ADEQUACY TEST
--
-- Round78 B2 only sees the pressure Hessian through the vorticity contraction
--
--   omega^T H omega
--
-- inside
--
--   W.W - omega^T H omega - additionalDepletion > 0.
--
-- Round85 already proves that the wider trace/Q + vorticity-contraction + one
-- injection record cannot determine arbitrary velocity-Hessian work.  Here we
-- strengthen that observation in the exact direction needed by C4:
-- **even a fixed strictly-positive B2 surplus does not determine the sign of
-- the Round86 principal velocity-Hessian work.**
--
-- Use omega=e2 and v=e1 with
--
--   Hminus = diag(-2,0, 2),
--   Hplus  = diag( 2,0,-2).
--
-- Both are trace free, both satisfy omega^T H omega=0, and both have the same
-- zero 23-injection.  Fix W.W=2 and additionalDepletion=1.  Then the B2 raw
-- surplus is exactly +1 for both Hessians, while
--
--   v^T Hminus v = -2,
--   v^T Hplus  v = +2.
--
-- Hence the current pressure-resolved dangerous-event scalar can coexist with
-- either sign of the C4a anisotropic principal work.  No estimate that requires
-- a one-sided sign for that work can be derived from the B2 record alone.
--
-- This is an information/implication countermodel, not a Navier--Stokes
-- solution counterexample.  The shortest repair is to derive or retain an
-- additional SAME-CONSUMER signed observable, e.g. the selected packet
-- velocity-Hessian pairing itself (or a theorem that bounds it one-sidedly
-- from stronger physical structure).  A Frobenius/source norm only supplies an
-- unsigned remainder budget and cannot create the missing sign.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _-_; _<_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)
import Data.Rational.Properties as ℚP
open ℚP using (_<?_)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as M
import DASHI.Physics.Closure.NSTriadKNCorrectedFourierAngularStrainExact as A
import DASHI.Physics.Closure.NSTriadKNPressureEnergyOperatorDeviatoricQRound85Exact as Energy

minusTwo plusTwo : ℚ
minusTwo = - (Int.+ 2)
plusTwo = Int.+ 2

omega : V.Vector3
omega = V.v3 0ℚ 1ℚ 0ℚ

velocity : V.Vector3
velocity = V.v3 1ℚ 0ℚ 0ℚ

hMinus hPlus : M.Matrix3
hMinus = M.matrix3
  minusTwo 0ℚ 0ℚ
  0ℚ 0ℚ 0ℚ
  0ℚ 0ℚ plusTwo

hPlus = M.matrix3
  plusTwo 0ℚ 0ℚ
  0ℚ 0ℚ 0ℚ
  0ℚ 0ℚ minusTwo

vorticityContraction : M.Matrix3 → ℚ
vorticityContraction H = V.dot omega (A.apply H omega)

velocityWork : M.Matrix3 → ℚ
velocityWork H = V.dot velocity (A.apply (Energy.deviatoric H) velocity)

frameInjection23 : M.Matrix3 → ℚ
frameInjection23 H =
  V.dot (V.v3 0ℚ 0ℚ 1ℚ) (A.apply H omega)

b2RawSurplus : M.Matrix3 → ℚ
b2RawSurplus H = plusTwo - vorticityContraction H - 1ℚ

traceMinusZero : Energy.matrixTrace hMinus ≡ 0ℚ
traceMinusZero = solve []

tracePlusZero : Energy.matrixTrace hPlus ≡ 0ℚ
tracePlusZero = solve []

qMinusZero : Energy.qFromTrace hMinus ≡ 0ℚ
qMinusZero = solve []

qPlusZero : Energy.qFromTrace hPlus ≡ 0ℚ
qPlusZero = solve []

vorticityContractionMinusZero : vorticityContraction hMinus ≡ 0ℚ
vorticityContractionMinusZero = solve []

vorticityContractionPlusZero : vorticityContraction hPlus ≡ 0ℚ
vorticityContractionPlusZero = solve []

injectionMinusZero : frameInjection23 hMinus ≡ 0ℚ
injectionMinusZero = solve []

injectionPlusZero : frameInjection23 hPlus ≡ 0ℚ
injectionPlusZero = solve []

sameB2RecordTrace : Energy.matrixTrace hMinus ≡ Energy.matrixTrace hPlus
sameB2RecordTrace = trans traceMinusZero (sym tracePlusZero)

sameB2RecordVorticityContraction :
  vorticityContraction hMinus ≡ vorticityContraction hPlus
sameB2RecordVorticityContraction =
  trans vorticityContractionMinusZero (sym vorticityContractionPlusZero)

sameB2RecordInjection : frameInjection23 hMinus ≡ frameInjection23 hPlus
sameB2RecordInjection = trans injectionMinusZero (sym injectionPlusZero)

b2SurplusMinusIsOne : b2RawSurplus hMinus ≡ 1ℚ
b2SurplusMinusIsOne = solve []

b2SurplusPlusIsOne : b2RawSurplus hPlus ≡ 1ℚ
b2SurplusPlusIsOne = solve []

sameB2Surplus : b2RawSurplus hMinus ≡ b2RawSurplus hPlus
sameB2Surplus = trans b2SurplusMinusIsOne (sym b2SurplusPlusIsOne)

b2SurplusStrictlyPositiveMinus : 0ℚ < b2RawSurplus hMinus
b2SurplusStrictlyPositiveMinus = toWitness {a? = 0ℚ <? b2RawSurplus hMinus} _

b2SurplusStrictlyPositivePlus : 0ℚ < b2RawSurplus hPlus
b2SurplusStrictlyPositivePlus = toWitness {a? = 0ℚ <? b2RawSurplus hPlus} _

velocityWorkMinus : velocityWork hMinus ≡ minusTwo
velocityWorkMinus = solve []

velocityWorkPlus : velocityWork hPlus ≡ plusTwo
velocityWorkPlus = solve []

record B2RecordDeterminesC4aVelocityWork : Set where
  field
    determine :
      (left right : M.Matrix3) →
      Energy.matrixTrace left ≡ Energy.matrixTrace right →
      vorticityContraction left ≡ vorticityContraction right →
      frameInjection23 left ≡ frameInjection23 right →
      b2RawSurplus left ≡ b2RawSurplus right →
      velocityWork left ≡ velocityWork right

open B2RecordDeterminesC4aVelocityWork public

b2RecordCannotDetermineC4aVelocityWork :
  B2RecordDeterminesC4aVelocityWork → minusTwo ≡ plusTwo
b2RecordCannotDetermineC4aVelocityWork candidate =
  trans
    (sym velocityWorkMinus)
    (trans
      (determine candidate hMinus hPlus
        sameB2RecordTrace
        sameB2RecordVorticityContraction
        sameB2RecordInjection
        sameB2Surplus)
      velocityWorkPlus)

round87PositiveB2SurplusDoesNotDetermineC4aPressureWorkSign : Bool
round87PositiveB2SurplusDoesNotDetermineC4aPressureWorkSign = true

round87C4aNeedsSameConsumerSignedPressureInformation : Bool
round87C4aNeedsSameConsumerSignedPressureInformation = true

round87UnsignedFrobeniusBoundCanCreateDangerousEventSign : Bool
round87UnsignedFrobeniusBoundCanCreateDangerousEventSign = false

round87PositiveB2SurplusDoesNotDetermineC4aPressureWorkSignIsTrue :
  round87PositiveB2SurplusDoesNotDetermineC4aPressureWorkSign ≡ true
round87PositiveB2SurplusDoesNotDetermineC4aPressureWorkSignIsTrue = refl

round87UnsignedFrobeniusBoundCanCreateDangerousEventSignIsFalse :
  round87UnsignedFrobeniusBoundCanCreateDangerousEventSign ≡ false
round87UnsignedFrobeniusBoundCanCreateDangerousEventSignIsFalse = refl
