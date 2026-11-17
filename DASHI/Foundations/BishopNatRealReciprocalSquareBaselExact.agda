module DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact where

------------------------------------------------------------------------
-- EMBEDDED NAT RECIPROCAL SQUARE = BASEL TERM
--
-- For k = n+1, identify the constructive reciprocal square of the embedded Nat
-- with the exact Basel sequence term already used by the convergence owner:
--
--   inverseSquare (natReal (n+1))  ~=  baselTerm n.
--
-- This is the literal compatibility bridge needed by the k-major Erdős sum.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Integer.Base as ℤ using (+_; +≤+)
open import Data.Rational.Unnormalised as ℚ using
  (ℚᵘ; 0ℚᵘ; 1ℚᵘ; _/_; _*_; _≤_; *≤*; _≃_; *≡*)

open import Data.Nat.Base using (z≤n; s≤s)
import Data.Rational.Unnormalised.Properties as ℚP
import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel
import DASHI.Foundations.BishopCubicTranslationIteratedExact as Iterated
import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal
import DASHI.Foundations.BishopInverseSquareProductExact as InverseProduct
import DASHI.Foundations.BishopNatRealPositiveExact as NatPositive
import DASHI.Mathematics.NumberTheory.FiniteNatRationalEmbeddingExact as NatEmbed
open import DASHI.Physics.YangMills.CompactLieProofLevel

reciprocalNatRational : Nat → ℚᵘ
reciprocalNatRational n = + 1 / suc n

reciprocalNatCancels :
  ∀ n →
  (reciprocalNatRational n ℚ.* NatEmbed.natAsRational (suc n))
  ℚ.≃ 1ℚᵘ
reciprocalNatCancels n = ℚ.*≡* refl

reciprocalNatSquareIsBaselRational :
  ∀ n →
  (reciprocalNatRational n ℚ.* reciprocalNatRational n)
  ℚ.≃ Basel.baselRationalTerm n
reciprocalNatSquareIsBaselRational n = ℚ.*≡* refl

embeddedReciprocalNatCancels :
  ∀ n →
  BishopReal._≃_
    (BishopReal._*_
      (Basel.embed (reciprocalNatRational n))
      (Iterated.natReal (suc n)))
    BishopReal.1ℝ
embeddedReciprocalNatCancels n =
  BishopP.≃-trans
    (BishopP.≃-symm
      (BishopP.⋆-distrib-*
        (reciprocalNatRational n)
        (NatEmbed.natAsRational (suc n))))
    (BishopP.⋆-cong (reciprocalNatCancels n))

natRealInverseIsEmbeddedReciprocal :
  ∀ n →
  BishopReal._≃_
    (InverseProduct.inverse
      (Iterated.natReal (suc n))
      (Reciprocal.xNonzero
        (NatPositive.natRealSuccessorStrictlyPositive n)))
    (Basel.embed (reciprocalNatRational n))
natRealInverseIsEmbeddedReciprocal n =
  InverseProduct.inverseFromCancellation
    (Iterated.natReal (suc n))
    (Basel.embed (reciprocalNatRational n))
    (Reciprocal.xNonzero
      (NatPositive.natRealSuccessorStrictlyPositive n))
    (embeddedReciprocalNatCancels n)

natRealSuccessorInverseSquareIsBaselTerm :
  ∀ n →
  BishopReal._≃_
    (Reciprocal.inverseSquare
      (Iterated.natReal (suc n))
      (Reciprocal.xNonzero
        (NatPositive.natRealSuccessorStrictlyPositive n)))
    (Basel.baselTerm n)
natRealSuccessorInverseSquareIsBaselTerm n =
  BishopP.≃-trans
    (BishopP.*-cong
      (natRealInverseIsEmbeddedReciprocal n)
      (natRealInverseIsEmbeddedReciprocal n))
    (BishopP.≃-trans
      (BishopP.≃-symm
        (BishopP.⋆-distrib-*
          (reciprocalNatRational n)
          (reciprocalNatRational n)))
      (BishopP.⋆-cong
        (reciprocalNatSquareIsBaselRational n)))

bishopNatRealReciprocalSquareBaselLevel : ProofLevel
bishopNatRealReciprocalSquareBaselLevel = machineChecked


------------------------------------------------------------------------
-- K04d: ALL INTEGER POWERS >= 2 OF THE *ORIGINAL* NAT RECIPROCAL
-- ARE DOMINATED BY THE SAME BASEL COEFFICIENT.
--
-- The proof never invokes logarithm/exponential/inverse function
-- semantics. It is a genuine rational-to-vendored-Bishop order lemma.
-- The standard expAdd + source log-inverse proof can reuse it to
-- discharge the integer real-axis portion of K04d-REGION.
------------------------------------------------------------------------

reciprocalAtMostOne :
  (n : Nat) →
  BishopReal._≤_
    (Basel.embed (reciprocalNatRational n))
    BishopReal.1ℝ
reciprocalAtMostOne n =
  BishopP.p≤q⇒p⋆≤q⋆
    (reciprocalNatRational n) 1ℚᵘ
    (ℚ.*≤* (ℤ.+≤+ (s≤s z≤n)))

reciprocalNonnegative :
  (n : Nat) →
  BishopReal.NonNegative
    (Basel.embed (reciprocalNatRational n))
reciprocalNonnegative n =
  BishopP.0≤x⇒nonNegx
    (BishopP.p≤q⇒p⋆≤q⋆
      ℚ.0ℚᵘ (reciprocalNatRational n)
      (ℚP.nonNegative⁻¹ (reciprocalNatRational n)))

oneToAnyNatPower : (k : Nat) →
  BishopReal._≃_
    (BishopReal.pow BishopReal.1ℝ k)
    BishopReal.1ℝ
oneToAnyNatPower zero = BishopP.≃-refl
oneToAnyNatPower (suc k) =
  BishopP.≃-trans
    (BishopP.*-congʳ (oneToAnyNatPower k))
    (BishopP.*-identityˡ BishopReal.1ℝ)

reciprocalPowersAtMostOne :
  (n k : Nat) →
  BishopReal._≤_
    (BishopReal.pow
      (Basel.embed (reciprocalNatRational n)) k)
    BishopReal.1ℝ
reciprocalPowersAtMostOne n k =
  BishopP.≤-respʳ-≃
    (oneToAnyNatPower k)
    (BishopSequence.x≤y∧nonNegx⇒xⁿ≤yⁿ
      k (reciprocalAtMostOne n) (reciprocalNonnegative n))

reciprocalExtraPowersBelowSquare :
  (n k : Nat) →
  let q = Basel.embed (reciprocalNatRational n)
  in
  BishopReal._≤_
    (BishopReal.pow q (suc (suc k)))
    (BishopReal.pow q (suc (suc zero)))
reciprocalExtraPowersBelowSquare n k =
  let
    q = Basel.embed (reciprocalNatRational n)
    qSquare = BishopReal.pow q (suc (suc zero))
    qSquareNN =
      BishopSequence.nonNegx⇒nonNegxⁿ
        (suc (suc zero)) (reciprocalNonnegative n)
    productBound =
      BishopP.*-monoˡ-≤-nonNeg
        (reciprocalPowersAtMostOne n k)
        qSquareNN
  in
  BishopP.≤-respˡ-≃
    (BishopP.xⁿxᵐ≃xⁿ⁺ᵐ q (suc (suc zero)) k)
    (BishopP.≤-respʳ-≃
      (BishopP.*-identityʳ qSquare)
      productBound)
