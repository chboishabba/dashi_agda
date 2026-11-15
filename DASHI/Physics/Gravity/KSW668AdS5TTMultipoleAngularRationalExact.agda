module DASHI.Physics.Gravity.KSW668AdS5TTMultipoleAngularRationalExact where

------------------------------------------------------------------------
-- Original 5D a=t brane compact TT 3-space angular source decomposition.
-- For axis k along x and Q=diag(0,1,-1), local order-four
-- TT Fourier symbol S_yy(k) = k^4 * (mu^4+6mu^2+1)/8.
--
-- The exact Legendre identity:
--   (mu^4+6mu^2+1)/8
--      = (2/5)P_0(mu)+(4/7)P_2(mu)+(1/35)P_4(mu).
-- This proves the FINITE THREE-MULTIPOLE algebra, not the original
-- continuum Fourier transform, PDE separation, source sampling or
-- numerical receiver convergence. Those separate analytic witnesses
-- are stated and checked in the source-equivalent SymPy/Numba owner.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_; -_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

p0 : ℚ → ℚ
p0 μ = 1ℚ

p2 : ℚ → ℚ
p2 μ = (((+ 3) / 1) * (μ * μ) + - 1ℚ) * ((+ 1) / 2)

p4 : ℚ → ℚ
p4 μ = (((+ 35) / 1) * ((μ * μ) * (μ * μ))
  + - (((+ 30) / 1) * (μ * μ)) + ((+ 3) / 1))
  * ((+ 1) / 8)

originalTTYYAngular : ℚ → ℚ
originalTTYYAngular μ =
  (((μ * μ) * (μ * μ)) + ((+ 6) / 1) * (μ * μ) + 1ℚ)
    * ((+ 1) / 8)

originalTTThreeMultipoles : ∀ μ →
  originalTTYYAngular μ ≡
    ((+ 2) / 5) * p0 μ
    + ((+ 4) / 7) * p2 μ
    + ((+ 1) / 35) * p4 μ
originalTTThreeMultipoles = ℚRing.solve-∀

p0AtReceiverAxis : p0 1ℚ ≡ 1ℚ
p0AtReceiverAxis = ℚRing.solve-∀

p2AtReceiverAxis : p2 1ℚ ≡ 1ℚ
p2AtReceiverAxis = ℚRing.solve-∀

p4AtReceiverAxis : p4 1ℚ ≡ 1ℚ
p4AtReceiverAxis = ℚRing.solve-∀

-- For H_ell=r^ell V_ell the 3D Laplacian's l(l+1)/r²
-- term cancels, leaving effective radial dimension 3+2*ell.
effRadialDimension : Nat → Nat
effRadialDimension ell = 3 + 2 * ell

ell0IsThreeDimensional : effRadialDimension 0 ≡ 3
ell0IsThreeDimensional = refl

ell2IsSevenDimensional : effRadialDimension 2 ≡ 7
ell2IsSevenDimensional = refl

ell4IsElevenDimensional : effRadialDimension 4 ≡ 11
ell4IsElevenDimensional = refl

-- No claim of pinned Agda 2.9 acceptance or full smooth moving PDE.
