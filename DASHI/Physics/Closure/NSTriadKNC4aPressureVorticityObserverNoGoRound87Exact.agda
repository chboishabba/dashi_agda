module DASHI.Physics.Closure.NSTriadKNC4aPressureVorticityObserverNoGoRound87Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Koji Ohkitani; Shigeo Kishiba.
-- Title: "Nonlocal nature of vortex stretching in an inviscid fluid".
-- Physics of Fluids 7 (1995), 411--421.
-- DOI: 10.1063/1.868633.
--
-- Authors: Dhawal Buaria; Alain Pumir.
-- Title: "Role of pressure in the dynamics of intense velocity gradients in
-- turbulent flows".
-- Journal of Fluid Mechanics 973 (2023), A23.
-- DOI: 10.1017/jfm.2023.786.
--
-- ROUND87 / C4a SAME-CONSUMER FALSIFIER
--
-- Round78 controls pressure through vorticity-facing scalars such as
--
--     Q,  omega^T H^D omega.
--
-- Round86 shows that the compact-transfer principal pressure consumer is
-- instead
--
--     v^T H^D v - (1/3) Q |v|^2,
--
-- where v is the selected packet velocity leg in the pressure-energy pairing.
-- These are different observers of the same trace-free Hessian.  The following
-- exact rational witness proves that the Round78 pair cannot determine the
-- Round86 anisotropic work without an additional relation between v and omega
-- (or a norm/operator estimate on H^D itself).
--
-- Take
--
--     H(a) = diag(a,-a,0),   omega=e3,   v=e1.
--
-- Then for every a,
--
--     tr H(a)=0,  Q=0,  omega^T H(a) omega=0,
--
-- while
--
--     v^T H(a) v=a.
--
-- In particular H(1) and H(2) collide on every Q/vorticity contraction used
-- by this witness but give different C4a principal work.  This is not an NS
-- counterexample; it is an exact information/adequacy obstruction showing that
-- C4a must be proved on the velocity consumer itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as M
import DASHI.Physics.Closure.NSTriadKNCorrectedFourierAngularStrainExact as A
import DASHI.Physics.Closure.NSTriadKNPressureEnergyOperatorDeviatoricQRound85Exact as Energy

zero one two : ℚ
zero = 0ℚ
one = 1ℚ
two = Int.+ 2

hessianFamily : ℚ → M.Matrix3
hessianFamily a =
  M.matrix3 a zero zero
            zero (zero - a) zero
            zero zero zero

omega : V.Vector3
omega = V.v3 zero zero one

packetVelocityDirection : V.Vector3
packetVelocityDirection = V.v3 one zero zero

traceFamilyZero : ∀ a → Energy.matrixTrace (hessianFamily a) ≡ zero
traceFamilyZero a = solve (a ∷ [])

qFamilyZero : ∀ a → Energy.qFromTrace (hessianFamily a) ≡ zero
qFamilyZero a = solve (a ∷ [])

vorticityDeviatoricContraction : ℚ → ℚ
vorticityDeviatoricContraction a =
  V.dot omega (A.apply (Energy.deviatoric (hessianFamily a)) omega)

packetVelocityDeviatoricWork : ℚ → ℚ
packetVelocityDeviatoricWork a =
  V.dot packetVelocityDirection
    (A.apply (Energy.deviatoric (hessianFamily a)) packetVelocityDirection)

vorticityContractionFamilyZero : ∀ a →
  vorticityDeviatoricContraction a ≡ zero
vorticityContractionFamilyZero a = solve (a ∷ [])

packetVelocityWorkEqualsParameter : ∀ a →
  packetVelocityDeviatoricWork a ≡ a
packetVelocityWorkEqualsParameter a = solve (a ∷ [])

sameQAtOneTwo :
  Energy.qFromTrace (hessianFamily one)
  ≡ Energy.qFromTrace (hessianFamily two)
sameQAtOneTwo = refl

sameVorticityPressureObservationAtOneTwo :
  vorticityDeviatoricContraction one
  ≡ vorticityDeviatoricContraction two
sameVorticityPressureObservationAtOneTwo = refl

packetVelocityWorkAtOne : packetVelocityDeviatoricWork one ≡ one
packetVelocityWorkAtOne = refl

packetVelocityWorkAtTwo : packetVelocityDeviatoricWork two ≡ two
packetVelocityWorkAtTwo = refl

round87QAndVorticityPressureObservationDoNotDetermineC4aWork : Bool
round87QAndVorticityPressureObservationDoNotDetermineC4aWork = true

round87C4aNeedsVelocityAlignedOrOperatorNormPressureControl : Bool
round87C4aNeedsVelocityAlignedOrOperatorNormPressureControl = true

round87OldPressureVorticityScalarAloneClosesC4a : Bool
round87OldPressureVorticityScalarAloneClosesC4a = false

round87QAndVorticityPressureObservationDoNotDetermineC4aWorkIsTrue :
  round87QAndVorticityPressureObservationDoNotDetermineC4aWork ≡ true
round87QAndVorticityPressureObservationDoNotDetermineC4aWorkIsTrue = refl

round87OldPressureVorticityScalarAloneClosesC4aIsFalse :
  round87OldPressureVorticityScalarAloneClosesC4a ≡ false
round87OldPressureVorticityScalarAloneClosesC4aIsFalse = refl
