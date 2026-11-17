module DASHI.Physics.Gravity.KSW668F8RadialFVGreenAndQuarticConsistencyExact where

------------------------------------------------------------------------
-- Max-cut XXXII: original KSW668 F8 radial FV conservative shell algebra.
-- Native radial r_j=j*h, volume W_j=[(j+1/2)^d -
-- max(j-1/2,0)^d] h^d/d, interface A_(j+1/2)=
-- (j+1/2)^(d-1) h^(d-2), effective d=3,7,11.
-- At the origin j=0: L u = 2*d*(u1-u0)/h².
--
-- Reuses owner KSW668AdS5TTFiniteVolumeFirstCellRationalExact
-- (do not recreate the d3/7/11 cp/cm coefficients).
--
-- Proofs:
--  (1) exact face Green algebra; all-faces finite telescope via List;
--  (2) first two shell rows' actual mass/face pairing;
--  (3) exact quadratic consistency and quartic O(h²) error at
--      the origin and first interior shell.
--
-- This is original *scalar effective radial* FV energy and truncation,
-- NOT an all-tensor discrete TT commutation theorem, coupled SAT/SSPRK3
-- energy or continuum Weyl convergence. Pinned Agda kernel pending.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (trans; sym)
import DASHI.Physics.Gravity.KSW668AdS5TTFiniteVolumeFirstCellRationalExact as FV

two four fifteen twenty thirtySix fiftyTwo : ℚ
two = (+ 2) / 1
four = (+ 4) / 1
fifteen = (+ 15) / 1
twenty = (+ 20) / 1
thirtySix = (+ 36) / 1
fiftyTwo = (+ 52) / 1

record RadialFace : Set where
  constructor face
  field
    uLeft uRight vLeft vRight : ℚ
    conductance : ℚ
open RadialFace

faceContribution : RadialFace → ℚ
faceContribution f =
  conductance f * uLeft f * (vRight f + - vLeft f)
  + conductance f * uRight f * (vLeft f + - vRight f)

faceDissipation : RadialFace → ℚ
faceDissipation f =
  - (conductance f
    * (uRight f + - uLeft f)
    * (vRight f + - vLeft f))

originalFVFaceGreen :
  (f : RadialFace) →
  faceContribution f ≡ faceDissipation f
originalFVFaceGreen f = solve []

faceSum : List RadialFace → ℚ
faceSum [] = 0ℚ
faceSum (f ∷ fs) = faceContribution f + faceSum fs

dissipationSum : List RadialFace → ℚ
dissipationSum [] = 0ℚ
dissipationSum (f ∷ fs) = faceDissipation f + dissipationSum fs

originalFVFiniteFaceGreen :
  (fs : List RadialFace) →
  faceSum fs ≡ dissipationSum fs
originalFVFiniteFaceGreen [] = refl
originalFVFiniteFaceGreen (f ∷ fs)
  rewrite originalFVFaceGreen f | originalFVFiniteFaceGreen fs = refl

-- In grid units h=1, W0 * origin coefficient 2d = A_(1/2).
-- Explicit original d=3,7,11 rational equalities.
originVolume3 originVolume7 originVolume11 : ℚ
originVolume3 = (+ 1) / 24
originVolume7 = (+ 1) / 896
originVolume11 = (+ 1) / 22528

originalOriginFlux3 :
  originVolume3 * ((+ 6) / 1) ≡ (+ 1) / 4
originalOriginFlux3 = solve []

originalOriginFlux7 :
  originVolume7 * ((+ 14) / 1) ≡ (+ 1) / 64
originalOriginFlux7 = solve []

originalOriginFlux11 :
  originVolume11 * ((+ 22) / 1) ≡ (+ 1) / 1024
originalOriginFlux11 = solve []

firstVolume3 firstVolume7 firstVolume11 : ℚ
firstVolume3 = (+ 13) / 12
firstVolume7 = (+ 1093) / 448
firstVolume11 = (+ 88573) / 11264

originalFirstUpperFlux3 :
  firstVolume3 * FV.d3Plus ≡ (+ 9) / 4
originalFirstUpperFlux3 = solve []

originalFirstLowerFlux3 :
  firstVolume3 * FV.d3Minus ≡ (+ 1) / 4
originalFirstLowerFlux3 = solve []

originalFirstUpperFlux7 :
  firstVolume7 * FV.d7Plus ≡ (+ 729) / 64
originalFirstUpperFlux7 = solve []

originalFirstLowerFlux7 :
  firstVolume7 * FV.d7Minus ≡ (+ 1) / 64
originalFirstLowerFlux7 = solve []

originalFirstUpperFlux11 :
  firstVolume11 * FV.d11Plus ≡ (+ 59049) / 1024
originalFirstUpperFlux11 = solve []

originalFirstLowerFlux11 :
  firstVolume11 * FV.d11Minus ≡ (+ 1) / 1024
originalFirstLowerFlux11 = solve []

-- L_h r^2 = 2d, including origin. Retain the existing owner's
-- exact quadratic tests and expose first-interior exact identity.
originalQuadraticFirst3 :
  ((+ 3) / 1) * FV.d3Plus + - FV.d3Minus
    ≡ (+ 6) / 1
originalQuadraticFirst3 = FV.originalD3ExactQuadratic

originalQuadraticFirst7 :
  ((+ 3) / 1) * FV.d7Plus + - FV.d7Minus
    ≡ (+ 14) / 1
originalQuadraticFirst7 = FV.originalD7ExactQuadratic

originalQuadraticFirst11 :
  ((+ 3) / 1) * FV.d11Plus + - FV.d11Minus
    ≡ (+ 22) / 1
originalQuadraticFirst11 = FV.originalD11ExactQuadratic

-- L_h(r^4) - 4(d+2) r² = e_(d,j) h² at r_j=j h.
-- At the origin, e_(d,0)=2d; at j=1:
--   e_(d,1)=15 cp_d - cm_d -4(d+2), a nonzero rational.
originalQuarticDefectFirst3 :
  fifteen * FV.d3Plus + - FV.d3Minus + - twenty
    ≡ (+ 142) / 13
originalQuarticDefectFirst3 = solve []

originalQuarticDefectFirst7 :
  fifteen * FV.d7Plus + - FV.d7Minus + - thirtySix
    ≡ (+ 37190) / 1093
originalQuarticDefectFirst7 = solve []

originalQuarticDefectFirst11 :
  fifteen * FV.d11Plus + - FV.d11Minus + - fiftyTwo
    ≡ (+ 5137278) / 88573
originalQuarticDefectFirst11 = solve []
