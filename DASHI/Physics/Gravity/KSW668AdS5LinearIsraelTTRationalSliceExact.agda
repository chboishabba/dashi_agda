module DASHI.Physics.Gravity.KSW668AdS5LinearIsraelTTRationalSliceExact where

-- Original 5D AdS a(t)=t cosmological brane, kappa5^2=6.
-- Linearised mixed-index Z2 Israel tensor channel:
-- (1/2) n·partial H_i^j = -(kappa5^2/2) pi_i^j = -3 pi_i^j.
-- H is dimensionless relative to q_ij=a^2(delta_ij+H_ij).
-- A spurious Robin term on this dimensionless H is NOT licensed.
-- Two TT polarisations, k along x; rational source slice only.
-- Does not prove moving-boundary Green existence, physical stress
-- generation, or the analytic differential geometry in Agda.
open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

data Spatial : Set where
  x y z : Spatial

piTT : Spatial → Spatial → ℚ
piTT y y = (+ 1) / 8
piTT z z = - ((+ 1) / 8)
piTT y z = (+ 1) / 12
piTT z y = (+ 1) / 12
piTT _ _ = 0ℚ

normalDerivativeH : Spatial → Spatial → ℚ
normalDerivativeH y y = - ((+ 3) / 4)
normalDerivativeH z z = (+ 3) / 4
normalDerivativeH y z = - ((+ 1) / 2)
normalDerivativeH z y = - ((+ 1) / 2)
normalDerivativeH _ _ = 0ℚ

linearIsraelTT :
  (i j : Spatial) →
  ((+ 1) / 2) * normalDerivativeH i j
    ≡ - (((+ 3) / 1) * piTT i j)
linearIsraelTT x x = solve []
linearIsraelTT x y = solve []
linearIsraelTT x z = solve []
linearIsraelTT y x = solve []
linearIsraelTT y y = solve []
linearIsraelTT y z = solve []
linearIsraelTT z x = solve []
linearIsraelTT z y = solve []
linearIsraelTT z z = solve []

transverseX1 : piTT x x ≡ 0ℚ
transverseX1 = solve []
transverseX2 : piTT x y ≡ 0ℚ
transverseX2 = solve []
transverseX3 : piTT x z ≡ 0ℚ
transverseX3 = solve []

traceZero : piTT x x + piTT y y + piTT z z ≡ 0ℚ
traceZero = solve []
