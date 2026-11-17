module DASHI.Physics.Gravity.KSW668F8TTSymbolDiscreteCompatibilityExact where

------------------------------------------------------------------------
-- Maximum-cut XXXI: SAME original F8 fourth-order TT symbol.
-- Q = diag(0,1,-1), P_ij(k)=|k|² delta_ij-k_i k_j,
-- T_ij(k)= (PQP)_ij - (1/2) P_ij tr(PQ).
-- Finite rational identities hold for ALL three rational derivative
-- symbols (a,b,c). The same algebra can be used with any CONSISTENT
-- discrete derivative symbol q_h, NOT with independently mixed symbols.
--
-- No derivative-symbol equality between original FV radial/normal
-- operators and Cartesian tensor differentiation is asserted here.
-- Exact counterexample demonstrates why that gate is necessary.
-- Original F8 generator authorship preserved. Agda kernel pending.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

half : ℚ
half = (+ 1) / 2

pxx pyy pzz pxy pxz pyz : ℚ → ℚ → ℚ → ℚ
pxx a b c = b * b + c * c
pyy a b c = a * a + c * c
pzz a b c = a * a + b * b
pxy a b c = - (a * b)
pxz a b c = - (a * c)
pyz a b c = - (b * c)

tracePQ : ℚ → ℚ → ℚ → ℚ
tracePQ a b c = pyy a b c + - pzz a b c

ttXX ttXY ttXZ ttYY ttYZ ttZZ : ℚ → ℚ → ℚ → ℚ
ttXX a b c =
  pxy a b c * pxy a b c
  + - (pxz a b c * pxz a b c)
  + - (half * pxx a b c * tracePQ a b c)
ttXY a b c =
  pxy a b c * pyy a b c
  + - (pxz a b c * pyz a b c)
  + - (half * pxy a b c * tracePQ a b c)
ttXZ a b c =
  pxy a b c * pyz a b c
  + - (pxz a b c * pzz a b c)
  + - (half * pxz a b c * tracePQ a b c)
ttYY a b c =
  pyy a b c * pyy a b c
  + - (pyz a b c * pyz a b c)
  + - (half * pyy a b c * tracePQ a b c)
ttYZ a b c =
  pyy a b c * pyz a b c
  + - (pyz a b c * pzz a b c)
  + - (half * pyz a b c * tracePQ a b c)
ttZZ a b c =
  pyz a b c * pyz a b c
  + - (pzz a b c * pzz a b c)
  + - (half * pzz a b c * tracePQ a b c)

-- Each row uses the SAME three derivative symbols as its projector.
originalTTTransverseX :
  (a b c : ℚ) →
  a * ttXX a b c + b * ttXY a b c + c * ttXZ a b c
    ≡ 0ℚ
originalTTTransverseX a b c = solve []

originalTTTransverseY :
  (a b c : ℚ) →
  a * ttXY a b c + b * ttYY a b c + c * ttYZ a b c
    ≡ 0ℚ
originalTTTransverseY a b c = solve []

originalTTTransverseZ :
  (a b c : ℚ) →
  a * ttXZ a b c + b * ttYZ a b c + c * ttZZ a b c
    ≡ 0ℚ
originalTTTransverseZ a b c = solve []

originalTTTraceless :
  (a b c : ℚ) →
  ttXX a b c + ttYY a b c + ttZZ a b c ≡ 0ℚ
originalTTTraceless a b c = solve []

-- Exact control: original symbol (1,2,3) vs incompatible divergence
-- symbol (1,1,2). Original symbol is TT, mixed one is NOT.
originalSymbolMixedDivergenceX :
  ttXX ((+ 1) / 1) ((+ 2) / 1) ((+ 3) / 1)
  + ttXY ((+ 1) / 1) ((+ 2) / 1) ((+ 3) / 1)
  + ((+ 2) / 1) * ttXZ ((+ 1) / 1) ((+ 2) / 1) ((+ 3) / 1)
    ≡ - ((+ 3) / 2)
originalSymbolMixedDivergenceX = solve []

originalSymbolMixedDivergenceY :
  ttXY ((+ 1) / 1) ((+ 2) / 1) ((+ 3) / 1)
  + ttYY ((+ 1) / 1) ((+ 2) / 1) ((+ 3) / 1)
  + ((+ 2) / 1) * ttYZ ((+ 1) / 1) ((+ 2) / 1) ((+ 3) / 1)
    ≡ - ((+ 24) / 1)
originalSymbolMixedDivergenceY = solve []

originalSymbolMixedDivergenceZ :
  ttXZ ((+ 1) / 1) ((+ 2) / 1) ((+ 3) / 1)
  + ttYZ ((+ 1) / 1) ((+ 2) / 1) ((+ 3) / 1)
  + ((+ 2) / 1) * ttZZ ((+ 1) / 1) ((+ 2) / 1) ((+ 3) / 1)
    ≡ (+ 33) / 2
originalSymbolMixedDivergenceZ = solve []

-- Quantified consistency target: tensor projector formed with symbol
-- (a,b,c), divergence applied with possibly different (u,v,w).
-- The entire leakage depends only on the DIFFERENCE of those symbols,
-- since the matching-symbol transverse sum is exactly zero.
mixedDivergenceX : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
mixedDivergenceX a b c u v w =
  u * ttXX a b c + v * ttXY a b c + w * ttXZ a b c
mixedDivergenceY : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
mixedDivergenceY a b c u v w =
  u * ttXY a b c + v * ttYY a b c + w * ttYZ a b c
mixedDivergenceZ : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
mixedDivergenceZ a b c u v w =
  u * ttXZ a b c + v * ttYZ a b c + w * ttZZ a b c

mixedDivergenceDefectX :
  (a b c u v w : ℚ) →
  mixedDivergenceX a b c u v w
  ≡ (u + - a) * ttXX a b c
    + (v + - b) * ttXY a b c
    + (w + - c) * ttXZ a b c
mixedDivergenceDefectX a b c u v w = solve []

mixedDivergenceDefectY :
  (a b c u v w : ℚ) →
  mixedDivergenceY a b c u v w
  ≡ (u + - a) * ttXY a b c
    + (v + - b) * ttYY a b c
    + (w + - c) * ttYZ a b c
mixedDivergenceDefectY a b c u v w = solve []

mixedDivergenceDefectZ :
  (a b c u v w : ℚ) →
  mixedDivergenceZ a b c u v w
  ≡ (u + - a) * ttXZ a b c
    + (v + - b) * ttYZ a b c
    + (w + - c) * ttZZ a b c
mixedDivergenceDefectZ a b c u v w = solve []
