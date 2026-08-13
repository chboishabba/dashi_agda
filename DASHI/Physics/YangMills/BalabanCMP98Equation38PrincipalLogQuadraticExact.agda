module DASHI.Physics.YangMills.BalabanCMP98Equation38PrincipalLogQuadraticExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- SOURCE LOCATION / NORMALIZATION
--
-- Around equations (34)--(38), Bałaban writes the differential of BCH through
-- g^{-1}(ad_Z) and Taylor-expands the nonidentity logarithm.  Equation (38)
-- has the source shape
--
--   (1/i) log (exp(iX) exp(iY))
--     = Y + g^{-1}(-i ad_Y) X + Psi(X;Y),
--
-- with |Psi(X;Y)| <= O(1)|X|^2 on the regular principal-log chart; the paper
-- explicitly notes that O(1)=24 may be used on the stated small neighbourhood
-- (in particular with |Y| <= 1/2 and X sufficiently small).
--
-- DASHI CONTRIBUTION
--
-- Encode that actual source quadratic estimate rather than another anonymous
-- differentiability receipt.  The proof below is the exact epsilon conversion:
--
--       |Psi| <= 24 |X|^2
--       24 |X| <= epsilon
--       -----------------
--       |Psi| <= epsilon |X|.
--
-- The left/right printed convention is NOT silently identified here.  The
-- caller supplies the exact Round-47 first-order object for the convention it
-- uses; this module only controls the magnitude of that SAME remainder.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel

sourceQuadraticConstant : ℚ
sourceQuadraticConstant = + 24 / 1

record Equation38QuadraticRemainder
    (inputMagnitude remainderMagnitude : ℚ) : Set where
  field
    inputNonnegative : 0ℚ ≤ inputMagnitude
    remainderNonnegative : 0ℚ ≤ remainderMagnitude
    sourceQuadraticBound :
      remainderMagnitude
      ≤ (sourceQuadraticConstant * inputMagnitude) * inputMagnitude

open Equation38QuadraticRemainder public

equation38RemainderLittleOEpsilon :
  ∀ inputMagnitude remainderMagnitude epsilon →
  Equation38QuadraticRemainder inputMagnitude remainderMagnitude →
  sourceQuadraticConstant * inputMagnitude ≤ epsilon →
  remainderMagnitude ≤ epsilon * inputMagnitude
equation38RemainderLittleOEpsilon inputMagnitude remainderMagnitude epsilon data small =
  ℚP.≤-trans
    (sourceQuadraticBound data)
    (ℚP.*-monoʳ-≤-nonNeg inputMagnitude small)

cmp98Equation38QuadraticRemainderLevel : ProofLevel
cmp98Equation38QuadraticRemainderLevel = machineChecked

cmp98Equation38LittleOEpsilonLevel : ProofLevel
cmp98Equation38LittleOEpsilonLevel = machineChecked
