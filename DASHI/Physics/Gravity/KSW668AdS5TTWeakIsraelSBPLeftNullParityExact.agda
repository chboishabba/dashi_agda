module DASHI.Physics.Gravity.KSW668AdS5TTWeakIsraelSBPLeftNullParityExact where

------------------------------------------------------------------------
-- KSW XI scoped original centered diagonal SBP2 physical constraint.
-- Original C=Dy U-(P-M)/2, mode3 SAT_P/SAT_M fixed. Correcting
-- ONLY U_T by a vector K requires Dy K=g, where g has independent
-- Neumann-wall and outer-normal endpoints.
--
-- Dy has left-kernel parity vector
--   ell(0)=(-1)^(n-1), ell(j)=2(-1)^(n-1-j), ell(n-1)=1.
-- Thus necessary compatibility:
--   (-1)^(n-1)*g_wall + g_far = 0.
--
-- Below are exact RATIONAL COLUMN identities for genuine n=3 and
-- n=4 SBP2 grids and explicit incompatible endpoint witnesses.
-- The arbitrary-n alternating-vector induction/finite-matrix bridge
-- is independently in the Python/SymPy owner; not Agda-accepted.
-- This DOES NOT rule out joint P,M,U SAT, a modified discrete
-- constraint, or a nonlocal, energy-compatible boundary repair.
------------------------------------------------------------------------
open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

half : ℚ
half = (+ 1) / 2

-- Three nodes: D=[[-1,1,0],[-1/2,0,1/2],[0,-1,1]]
-- Exact left null [1,-2,1] column by column.
n3LeftColumn0 : - 1ℚ + ((- ((+ 2) / 1)) * (- half)) ≡ 0ℚ
n3LeftColumn0 = ℚRing.solve []

n3LeftColumn1 : 1ℚ + - 1ℚ ≡ 0ℚ
n3LeftColumn1 = ℚRing.solve []

n3LeftColumn2 : ((- ((+ 2) / 1)) * half) + 1ℚ ≡ 0ℚ
n3LeftColumn2 = ℚRing.solve []

n3BadEndpoints :
  1ℚ * 1ℚ + 1ℚ * ((+ 2) / 1) ≡ ((+ 3) / 1)
n3BadEndpoints = ℚRing.solve []

-- Four nodes: left null [-1,2,-2,1].
n4LeftColumn0 :
  (- 1ℚ) * (- 1ℚ) + ((+ 2) / 1) * (- half) ≡ 0ℚ
n4LeftColumn0 = ℚRing.solve []

n4LeftColumn1 :
  (- 1ℚ) * 1ℚ + (- ((+ 2) / 1)) * (- half) ≡ 0ℚ
n4LeftColumn1 = ℚRing.solve []

n4LeftColumn2 :
  ((+ 2) / 1) * half + 1ℚ * (- 1ℚ) ≡ 0ℚ
n4LeftColumn2 = ℚRing.solve []

n4LeftColumn3 :
  (- ((+ 2) / 1)) * half + 1ℚ ≡ 0ℚ
n4LeftColumn3 = ℚRing.solve []

n4BadEndpoints :
  (- 1ℚ) * 1ℚ + 1ℚ * ((+ 2) / 1) ≡ 1ℚ
n4BadEndpoints = ℚRing.solve []

-- With original n3/4 source residuals (g0,g_far)=(1,2),
-- the left-null pairings 3/1 cannot equal zero. No solution
-- Dy K=g exists in this restricted Udot-only repair class.
