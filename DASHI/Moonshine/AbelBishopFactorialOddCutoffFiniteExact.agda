module DASHI.Moonshine.AbelBishopFactorialOddCutoffFiniteExact where

------------------------------------------------------------------------
-- P1 ODD-CUTOFF EXACT REMAINDER, ON THE ORIGINAL BISHOP CARRIER.
--
-- S_(2N+1)(iy) - S_(2N)(iy) = (cosineTerm_N, 0).
-- This is an exact finite source identity, *not* a convergence claim.
-- The next analytic leaf is the source bound cosineTerm_N -> 0.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product.Base using (proj₁; proj₂)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimates
import DASHI.Moonshine.AbelBishopFactorialComplexImaginaryAxisFiniteReindexExact as EvenPrefix
import DASHI.Moonshine.AbelBishopFactorialComplexImaginaryAxisSignedTermsExact as Signed
import DASHI.Moonshine.AbelBishopFactorialComplexImaginaryAxisTwoStepExact as Axis

originalBishopImaginaryAxisRealOddPrefix :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ y n →
  BishopReal._≃_
    (BishopReal.∑₀
      (EvenPrefix.factorialImaginaryRealTerm y)
      (suc (Estimates.evenExponent n)))
    (BishopReal._+_
      (BishopReal.∑₀
        (Elementary.cosineTerm (Cartesian.dataSet T) y)
        n)
      (Elementary.cosineTerm (Cartesian.dataSet T) y n))
originalBishopImaginaryAxisRealOddPrefix T y n =
  BishopP.+-cong
    (EvenPrefix.originalBishopImaginaryAxisRealPrefix2NIsCosine T y n)
    (Signed.originalBishopImaginaryAxisCosineConfiguredTerm T y n)

originalBishopImaginaryAxisImagOddPrefix :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ y n →
  BishopReal._≃_
    (BishopReal.∑₀
      (EvenPrefix.factorialImaginaryImagTerm y)
      (suc (Estimates.evenExponent n)))
    (BishopReal.∑₀
      (Elementary.sineTerm (Cartesian.dataSet T) y)
      n)
originalBishopImaginaryAxisImagOddPrefix T y n =
  BishopP.≃-trans
    (BishopP.+-cong
      (EvenPrefix.originalBishopImaginaryAxisImagPrefix2NIsSine T y n)
      (proj₂ (Axis.originalBishopImaginaryAxisFactorialEvenTerm y n)))
    (BishopP.+-identityʳ
      (BishopReal.∑₀ (Elementary.sineTerm (Cartesian.dataSet T) y) n))

-- The difference between even- and odd-cutoff real prefixes is precisely
-- a single original *configured* cosine coefficient. No rearrangement.
originalBishopImaginaryAxisOddCutoffRemainder :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ y n →
  BishopReal._≃_
    (BishopReal._-_
      (BishopReal.∑₀
        (EvenPrefix.factorialImaginaryRealTerm y)
        (suc (Estimates.evenExponent n)))
      (BishopReal.∑₀
        (EvenPrefix.factorialImaginaryRealTerm y)
        (Estimates.evenExponent n)))
    (Elementary.cosineTerm (Cartesian.dataSet T) y n)
originalBishopImaginaryAxisOddCutoffRemainder T y n =
  let
    even = BishopReal.∑₀
      (EvenPrefix.factorialImaginaryRealTerm y)
      (Estimates.evenExponent n)
    coefficient = EvenPrefix.factorialImaginaryRealTerm y
      (Estimates.evenExponent n)
  in
  BishopP.≃-trans
    (let open BishopP.ℝ-Solver in
     solve 2
       (λ e a → (e ⊕ a) ⊖ e ⊜ a)
       BishopP.≃-refl even coefficient)
    (Signed.originalBishopImaginaryAxisCosineConfiguredTerm T y n)
