module DASHI.Physics.YangMills.YMClayP0BishopRealCarrierInstancesExact where

------------------------------------------------------------------------
-- P0.01 / P0.03 genuine CONSTRUCTED BISHOP REAL ARITHMETIC.
--
-- This is the real carrier provided by the pinned Murray/Csimma
-- constructive-reals implementation, NOT the distinct abstract
-- RealAnalysisAxioms.ℝ socket used by the current original Wilson
-- measure modules.
--
-- All theorems below have BISHOP SETOID EQUALITY (_≃_) and are
-- proved with the imported Bishop ℝ ring solver and inverse laws.
-- No new postulate, no quotient by definitional equality, and no
-- assumption of physical SU(N) RG estimates.
--
-- Status of the original Wilson P0 gate is still OPEN until an
-- identity-preserving same-carrier/quotient interpretation explicitly
-- transports these theorems to its RealAnalysisAxioms socket, including
-- the concrete Wilson 'divide' function and positive-partition order.
------------------------------------------------------------------------

open import Data.Sum.Base using (inj₂)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)

import Real as Bishop
import RealProperties as P
import Inverse as Inv

-- P0.01: real subtraction is additive inverse multiplication by 1,
-- on the actual constructive Bishop carrier, up to its native ≃.
bishopSubtractionAsNegationTimesUnit :
  (x c : Bishop.ℝ) →
  Bishop._≃_
    (Bishop._-_ x c)
    (Bishop._+_ x
      (Bishop._*_ (Bishop.-_ c) Bishop.1ℝ))
bishopSubtractionAsNegationTimesUnit x c =
  let open P.ℝ-Solver in
  solve 2
    (λ a b → (a ⊖ b) ⊜ (a ⊕ ((⊝ b) ⊗ Κ 1ℚᵘ)))
    P.≃-refl x c

-- The previously independent x-0=x scalar law has a direct
-- concrete Bishop-real source proof.
bishopSubtractionZeroRight :
  (x : Bishop.ℝ) →
  Bishop._≃_ (Bishop._-_ x Bishop.0ℝ) x
bishopSubtractionZeroRight x =
  let open P.ℝ-Solver in
  solve 1 (λ a → (a ⊖ Κ 0ℚᵘ) ⊜ a)
    P.≃-refl x

-- P0.04 scalar cancellation. Unlike a stored *assumption*, this
-- is an inhabited proof derived from the actual Bishop ring laws.
bishopCenteredScalarCancellation :
  (numerator value partition : Bishop.ℝ) →
  Bishop._≃_
    numerator
    (Bishop._*_ value partition) →
  Bishop._≃_
    (Bishop._+_ numerator
      (Bishop._*_ (Bishop.-_ value) partition))
    Bishop.0ℝ
bishopCenteredScalarCancellation numerator value partition numEq =
  P.≃-trans
    (P.+-cong numEq P.≃-refl)
    (let open P.ℝ-Solver in
     solve 2
       (λ v d →
         ((v ⊗ d) ⊕ ((⊝ v) ⊗ d)) ⊜ Κ 0ℚᵘ)
       P.≃-refl value partition)

-- A positive Bishop denominator has a CONSTRUCTED nonzero witness
-- (apartness) accepted by the library's genuinely defined inverse.
bishopPositiveDenominatorApartFromZero :
  (d : Bishop.ℝ) →
  Bishop._<_ Bishop.0ℝ d →
  d Bishop.≄0
bishopPositiveDenominatorApartFromZero d positive = inj₂ positive

-- P0.03: exact positive-division cancellation on the constructed
-- Bishop carrier, with no independently postulated divide operation.
-- The order proof is used to build a valid constructive inverse.
bishopPositiveQuotientTimesDenominator :
  (numerator denominator : Bishop.ℝ) →
  (positive : Bishop._<_ Bishop.0ℝ denominator) →
  Bishop._≃_
    (Bishop._*_
      (Bishop._*_ numerator
        (Inv._⁻¹ denominator
          (bishopPositiveDenominatorApartFromZero
            denominator positive)))
      denominator)
    numerator
bishopPositiveQuotientTimesDenominator numerator denominator positive =
  let apart = bishopPositiveDenominatorApartFromZero denominator positive
      reciprocal = Inv._⁻¹ denominator apart
  in P.≃-trans
       (P.*-assoc numerator reciprocal denominator)
       (P.≃-trans
         (P.*-congˡ (Inv.*-inverseˡ denominator apart))
         (P.*-identityʳ numerator))

-- The bare-centering scalar leaf is therefore also inhabited on
-- this same Bishop carrier, without invoking physical Haar laws.
bishopPositiveQuotientCenteredCancellation :
  (numerator denominator : Bishop.ℝ) →
  (positive : Bishop._<_ Bishop.0ℝ denominator) →
  let quotient =
        Bishop._*_ numerator
          (Inv._⁻¹ denominator
            (bishopPositiveDenominatorApartFromZero
              denominator positive))
  in Bishop._≃_
       (Bishop._+_ numerator
         (Bishop._*_ (Bishop.-_ quotient) denominator))
       Bishop.0ℝ
bishopPositiveQuotientCenteredCancellation numerator denominator positive =
  let apart = bishopPositiveDenominatorApartFromZero denominator positive
      quotient = Bishop._*_ numerator (Inv._⁻¹ denominator apart)
  in bishopCenteredScalarCancellation
       numerator quotient denominator
       (P.≃-symm
         (bishopPositiveQuotientTimesDenominator
           numerator denominator positive))
