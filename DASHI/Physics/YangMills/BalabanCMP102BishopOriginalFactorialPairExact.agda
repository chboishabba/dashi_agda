module DASHI.Physics.YangMills.BalabanCMP102BishopOriginalFactorialPairExact where

-- Original Bishop factorial summands for CMP102.
-- Uses existing exponential, source A/B, and concrete parity owners.
-- No replacement real, factorial, algebra carrier or physical admission.
-- These are POINTWISE lemmas: full parity-row transport remains open.
--
-- Provenance: Murray 2022; Csimma pinned bishop backend; original DASHI
-- finite exponential and Bałaban CMP109 root-free series owners.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Nat.Base as N
import Real as B
import RealProperties as P
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopSignedFactorialConvolutionExact as Signed
import DASHI.Physics.YangMills.BalabanCMP109BishopRootFreeSeriesExact as S
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as E
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Signs

-- Eliminate Nat truncated subtraction only after giving both indices.
-- The induction follows the actual builtin recursive addition/subtraction.
complementBySum : ∀ left right →
  (left N.+ right) N.∸ left ≡ right
complementBySum zero right = refl
complementBySum (suc left) right = complementBySum left right

evenFirst evenSecond oddFirst oddSecond : Nat → Nat
evenFirst k = E.evenExponent (suc k)
evenSecond r = E.evenExponent (suc r)
oddFirst k = E.oddExponent (suc k)
oddSecond r = E.oddExponent (suc r)

evenDegree oddDegree : Nat → Nat → Nat
evenDegree k r = evenFirst k N.+ evenSecond r
oddDegree k r = oddFirst k N.+ oddSecond r

evenComplement : ∀ k r →
  (evenDegree k r N.∸ evenFirst k) ≡ evenSecond r
evenComplement k r = complementBySum (evenFirst k) (evenSecond r)

oddComplement : ∀ k r →
  (oddDegree k r N.∸ oddFirst k) ≡ oddSecond r
oddComplement k r = complementBySum (oddFirst k) (oddSecond r)

-- The same factorial embedding is used by Exp and the native CMP109
-- A/B coefficients. Only the power of the real unit must be removed.
powerOne : ∀ n → B._≃_ (B.pow B.1ℝ n) B.1ℝ
powerOne zero = P.≃-refl
powerOne (suc n) =
  P.≃-trans
    (P.*-congʳ (powerOne n))
    (P.*-identityˡ B.1ℝ)

expOneIsInverseFactorial : ∀ n →
  B._≃_ (Exp.expTerm B.1ℝ n)
          (Exp.embed (Exp.inverseFactorial n))
expOneIsInverseFactorial n =
  P.≃-trans
    (P.*-congʳ (powerOne n))
    (P.*-identityˡ (Exp.embed (Exp.inverseFactorial n)))

originalAAsExpOne : ∀ k →
  B._≃_ (Exp.expTerm B.1ℝ (evenFirst k)) (S.aCoefficient k)
originalAAsExpOne k = expOneIsInverseFactorial (evenFirst k)

originalBAsExpOne : ∀ k →
  B._≃_ (Exp.expTerm B.1ℝ (oddFirst k)) (S.bCoefficient k)
originalBAsExpOne k = expOneIsInverseFactorial (oddFirst k)

-- The original signed source uses the MINUS ONE exponential in the
-- complementary factor. Even complementary exponents erase that sign.
evenSignedOriginalPair : ∀ k r →
  B._≃_
    (Signed.signedTerm (evenDegree k r) (evenFirst k))
    (B._*_ (S.aCoefficient k) (S.aCoefficient r))
evenSignedOriginalPair k r rewrite evenComplement k r =
  P.≃-trans
    (P.*-congˡ
      (P.*-congʳ
        (Signs.evenPowerNegation B.1ℝ (suc r))))
    (P.*-cong (originalAAsExpOne k) (originalAAsExpOne r))

-- Odd complementary exponents retain precisely one minus sign.
-- A ring identity moves the negation outside the ORIGINAL product.
oddSignedOriginalPair : ∀ k r →
  B._≃_
    (Signed.signedTerm (oddDegree k r) (oddFirst k))
    (B.- (B._*_ (S.bCoefficient k) (S.bCoefficient r)))
oddSignedOriginalPair k r rewrite oddComplement k r =
  let
    left = Exp.expTerm B.1ℝ (oddFirst k)
    rightPower = B.pow B.1ℝ (oddSecond r)
    coeff = Exp.embed (Exp.inverseFactorial (oddSecond r))
    open P.ℝ-Solver
  in
  P.≃-trans
    (P.*-congˡ
      (P.*-congʳ
        (Signs.oddPowerNegation B.1ℝ (suc r))))
    (P.≃-trans
      (solve 3
        (λ x p c → x ⊗ ((⊝ p) ⊗ c) ⊜ ⊝ (x ⊗ (p ⊗ c)))
        P.≃-refl left rightPower coeff)
      (P.-‿cong
        (P.*-cong (originalBAsExpOne k) (originalBAsExpOne r))))
