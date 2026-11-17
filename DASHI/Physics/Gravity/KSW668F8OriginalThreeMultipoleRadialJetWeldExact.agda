module DASHI.Physics.Gravity.KSW668F8OriginalThreeMultipoleRadialJetWeldExact where

-- Original H_ell=(r/eps)^ell V_ell, ell=0,2,4.
-- Exact ORIGINAL 3D spherical harmonic Laplacian cancellation, with
-- polynomial r²-weighted jets: no coordinate-axis division or invented
-- independent 7D/11D physical bulk. Kernel acceptance pending.
open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.Gravity.KSW668AdS5TTMultipoleAngularRationalExact as Angular

r2 : ℚ → ℚ
r2 r = r * r
r3 : ℚ → ℚ
r3 r = r2 r * r
r4 : ℚ → ℚ
r4 r = r2 r * r2 r
r5 : ℚ → ℚ
r5 r = r4 r * r
r6 : ℚ → ℚ
r6 r = r4 r * r2 r

two six ten twelve eighteen twenty : ℚ
two = (+ 2) / 1
six = (+ 6) / 1
ten = (+ 10) / 1
twelve = (+ 12) / 1
eighteen = (+ 18) / 1
twenty = (+ 20) / 1

-- c=eps^-ell is held fixed under r differentiation.
r2Hrr0 : ℚ → ℚ → ℚ → ℚ
r2Hrr0 c r vrr = c * r2 r * vrr
r2Lap0 : ℚ → ℚ → ℚ → ℚ → ℚ
r2Lap0 c r vr vrr = c * (r2 r * vrr + two * r * vr)

H2 : ℚ → ℚ → ℚ → ℚ
H2 c r v = c * r2 r * v
rHr2 : ℚ → ℚ → ℚ → ℚ → ℚ
rHr2 c r v vr = c * (r3 r * vr + two * r2 r * v)
r2Hrr2 : ℚ → ℚ → ℚ → ℚ → ℚ
r2Hrr2 c r v vr vrr =
  c * (r4 r * vrr + ((+ 4) / 1) * r3 r * vr + two * r2 r * v)
r2Lap2 : ℚ → ℚ → ℚ → ℚ → ℚ
r2Lap2 c r vr vrr = c * (r4 r * vrr + six * r3 r * vr)

H4 : ℚ → ℚ → ℚ → ℚ
H4 c r v = c * r4 r * v
rHr4 : ℚ → ℚ → ℚ → ℚ → ℚ
rHr4 c r v vr = c * (r5 r * vr + ((+ 4) / 1) * r4 r * v)
r2Hrr4 : ℚ → ℚ → ℚ → ℚ → ℚ
r2Hrr4 c r v vr vrr =
  c * (r6 r * vrr + ((+ 8) / 1) * r5 r * vr + twelve * r4 r * v)
r2Lap4 : ℚ → ℚ → ℚ → ℚ → ℚ
r2Lap4 c r vr vrr = c * (r6 r * vrr + ten * r5 r * vr)

-- r² Delta3 H = r² H_rr + 2r H_r - ell(ell+1) H
-- = c*r^ell*(r² V_rr+(2ell+2)r V_r), on Y_ell.
originalRadialLaplacianEll0 :
  (c r v vr vrr : ℚ) →
  r2Hrr0 c r vrr + two * c * r * vr
    ≡ r2Lap0 c r vr vrr
originalRadialLaplacianEll0 c r v vr vrr = solve []

originalRadialLaplacianEll2 :
  (c r v vr vrr : ℚ) →
  r2Hrr2 c r v vr vrr + two * rHr2 c r v vr
    + - (six * H2 c r v)
    ≡ r2Lap2 c r vr vrr
originalRadialLaplacianEll2 c r v vr vrr = solve []

originalRadialLaplacianEll4 :
  (c r v vr vrr : ℚ) →
  r2Hrr4 c r v vr vrr + two * rHr4 c r v vr
    + - (twenty * H4 c r v)
    ≡ r2Lap4 c r vr vrr
originalRadialLaplacianEll4 c r v vr vrr = solve []

-- Actual E5-2E4 radial combination: Lap3 H + H_rr.
originalWeylRadialCombinationEll2 :
  (c r v vr vrr : ℚ) →
  r2Lap2 c r vr vrr + r2Hrr2 c r v vr vrr
    ≡ c * (two * r4 r * vrr + ten * r3 r * vr
               + two * r2 r * v)
originalWeylRadialCombinationEll2 c r v vr vrr = solve []

originalWeylRadialCombinationEll4 :
  (c r v vr vrr : ℚ) →
  r2Lap4 c r vr vrr + r2Hrr4 c r v vr vrr
    ≡ c * (two * r6 r * vrr + eighteen * r5 r * vr
               + twelve * r4 r * v)
originalWeylRadialCombinationEll4 c r v vr vrr = solve []
