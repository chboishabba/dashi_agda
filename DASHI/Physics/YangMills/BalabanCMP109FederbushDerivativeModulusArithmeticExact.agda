module DASHI.Physics.YangMills.BalabanCMP109FederbushDerivativeModulusArithmeticExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Freeze the quantitative endpoint of the differentiated Federbush average so
-- the equation-(0.12) proof never recomputes it.  With
--
--   K(U)=J(U)T(U),
--   L_K = L_J C_T + C_J L_T,
-- normalized contour averaging preserves L_K.  The already proved 4/3
-- reopening and the resolvent identity give
--
--   L_{A^-1} = (16/9) L_K.
--
-- For DM(U)=A(U)^-1 b(U), if ||b(U)|| <= C_b and b has modulus L_b,
--
--   L_DM = (16/9) L_K C_b + (4/3) L_b.
--
-- This module proves the exact rational arithmetic and monotonicity used by
-- that endpoint.  Smallness is deliberately not required: these constants
-- control the O(t^2) tangent correction, not the already-closed Newton margin.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _/_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel

fourThirds sixteenNinths : ℚ
fourThirds = + 4 / 3
sixteenNinths = + 16 / 9

federbushComponentModulus : ℚ → ℚ → ℚ → ℚ → ℚ
federbushComponentModulus LJ CT CJ LT = LJ * CT + CJ * LT

federbushInverseModulus : ℚ → ℚ
federbushInverseModulus LK = sixteenNinths * LK

federbushAverageDerivativeModulus : ℚ → ℚ → ℚ → ℚ
federbushAverageDerivativeModulus LK Cb Lb =
  sixteenNinths * LK * Cb + fourThirds * Lb

componentModulusFormula : ∀ LJ CT CJ LT →
  federbushComponentModulus LJ CT CJ LT
  ≡ LJ * CT + CJ * LT
componentModulusFormula LJ CT CJ LT = refl

inverseModulusFormula : ∀ LK →
  federbushInverseModulus LK ≡ (+ 16 / 9) * LK
inverseModulusFormula LK = refl

averageDerivativeModulusFormula : ∀ LK Cb Lb →
  federbushAverageDerivativeModulus LK Cb Lb
  ≡ (+ 16 / 9) * LK * Cb + (+ 4 / 3) * Lb
averageDerivativeModulusFormula LK Cb Lb = refl

-- The product telescope at the level of scalar budgets.  This is the exact
-- arithmetic shape consumed by the finite column-mass theorem.
productVariationBudgetExact : ∀ LJ CT CJ LT delta →
  (LJ * delta) * CT + CJ * (LT * delta)
  ≡ federbushComponentModulus LJ CT CJ LT * delta
productVariationBudgetExact LJ CT CJ LT delta =
  ℚRing.solve-∀ LJ CT CJ LT delta

resolventVariationBudgetExact : ∀ LK delta →
  fourThirds * (LK * delta) * fourThirds
  ≡ federbushInverseModulus LK * delta
resolventVariationBudgetExact LK delta =
  ℚRing.solve-∀ LK delta

averageDerivativeVariationBudgetExact : ∀ LK Cb Lb delta →
  (federbushInverseModulus LK * delta) * Cb
    + fourThirds * (Lb * delta)
  ≡ federbushAverageDerivativeModulus LK Cb Lb * delta
averageDerivativeVariationBudgetExact LK Cb Lb delta =
  ℚRing.solve-∀ LK Cb Lb delta

-- Monotonicity in the two genuinely new local inputs L_J and L_T.  It lets a
-- physical proof use deliberately coarse finite constants without reopening
-- the downstream algebra.
componentModulusMonotone :
  ∀ {LJ LJ' CT CJ LT LT'} →
  0ℚ ≤ CT → 0ℚ ≤ CJ →
  LJ ≤ LJ' → LT ≤ LT' →
  federbushComponentModulus LJ CT CJ LT
  ≤ federbushComponentModulus LJ' CT CJ LT'
componentModulusMonotone {LJ} {LJ'} {CT} {CJ} {LT} {LT'}
    CTnn CJnn LJ≤ LT≤ =
  ℚP.+-mono-≤
    (let instance ctNN : NonNegative CT = ℚ.nonNegative CTnn
     in ℚP.*-monoʳ-≤-nonNeg CT LJ≤)
    (let instance cjNN : NonNegative CJ = ℚ.nonNegative CJnn
     in ℚP.*-monoˡ-≤-nonNeg CJ LT≤)

cmp109FederbushComponentModulusArithmeticLevel : ProofLevel
cmp109FederbushComponentModulusArithmeticLevel = machineChecked

cmp109FederbushInverseModulusArithmeticLevel : ProofLevel
cmp109FederbushInverseModulusArithmeticLevel = machineChecked

cmp109FederbushAverageDerivativeModulusArithmeticLevel : ProofLevel
cmp109FederbushAverageDerivativeModulusArithmeticLevel = machineChecked
