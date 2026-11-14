module DASHI.Moonshine.AbelBishopFactorialOddCutoffVanishingExact where

------------------------------------------------------------------------
-- EXPLICIT CONSTRUCTIVE ODD-CUTOFF FACTORIAL TAIL MODULUS.
--
-- The coefficient c_n(y) is EXACTLY the original configured
-- Bishop cosine coefficient, identified with the real coordinate
-- (iy)^(2n)/(2n)! by the preceding finite source weld.
--
-- The pinned Bishop Sequence.agda owns:
--    ∑xₙisConvergent⇒xₙ→0
-- and the cosine series has a concrete absolute-convergence proof.
-- Unpack the original con* witness to produce a natural cutoff
-- N(k) such that for all n>=N(k), |c_n(y)|<=1/k.
--
-- No postulate, new analytic authority, or classical epsilon choice.
-- The source is pending Agda 2.9 --safe kernel acceptance.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
import Data.Nat.Base as ℕ using (NonZero; _≤_)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (0ℚᵘ; _/_)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Moonshine.AbelBishopFactorialOddCutoffFiniteExact as Odd

originalBishopOddCutoffCosineModulus :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  (y : BishopReal.ℝ) →
  (k : Nat) → .{{_ : ℕ.NonZero k}} →
  Nat
originalBishopOddCutoffCosineModulus T y k
  with Odd.originalBishopConfiguredCosineTermTendsZero T y
... | BishopSequence.con* modulus =
  suc (proj₁ (modulus k))

originalBishopOddCutoffCosineBound :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  (y : BishopReal.ℝ) →
  (k : Nat) → .{{_ : ℕ.NonZero k}} →
  ∀ n →
  originalBishopOddCutoffCosineModulus T y k ℕ.≤ n →
  BishopReal._≤_
    (BishopReal.∣ Elementary.cosineTerm (Cartesian.dataSet T) y n ∣)
    (BishopReal._⋆ (+ 1 / k))
originalBishopOddCutoffCosineBound T y k n n≥
  with Odd.originalBishopConfiguredCosineTermTendsZero T y
... | BishopSequence.con* modulus =
  let
    coefficient = Elementary.cosineTerm (Cartesian.dataSet T) y n
    absoluteShift :
      BishopReal._≃_
        (BishopReal.∣ coefficient ∣)
        (BishopReal.∣ BishopReal._-_ coefficient BishopReal.0ℝ ∣)
    absoluteShift =
      BishopP.∣-∣-cong
        (let open BishopP.ℝ-Solver in
         solve 1
           (λ c → c ⊜ c ⊖ Κ 0ℚᵘ)
           BishopP.≃-refl coefficient)
  in
  BishopP.≤-respˡ-≃
    absoluteShift
    (proj₂ (modulus k) n n≥)
