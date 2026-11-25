module DASHI.Foundations.BishopChudnovskyFactorialSourceExact where

-- SOURCE-WRITTEN, UNCOMPILED. Same literal raw signed P/Q/T and
-- standard-library factorial. No imported analytic equality.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_!; _^_)
open import Data.Empty using (⊥-elim)
import Data.Nat.Base as N
import Data.Nat.Properties as NP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import Data.Integer.Base as Z
import Data.Integer.Properties as I
open import Data.Integer.Solver renaming (module +-*-Solver to ZSolver)
open ZSolver using () renaming
  (solve to zs; _:+_ to _⊕_; _:*_ to _⊗_; con to zk; _:=_ to _⊜_)
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
import DASHI.Foundations.BishopChudnovskyRationalMidpointExact as CH
import DASHI.Foundations.BishopChudnovskyIndexedEdgeAlgebraExact as E
import DASHI.Foundations.BishopChudnovskyPositiveGapExact as G
import DASHI.Foundations.BishopChudnovskyPrefixSemanticsExact as P

block3 : Nat → Nat
block3 n = (3 * n + 1) * (3 * n + 2) * (3 * n + 3)

block6 : Nat → Nat
block6 n = (6 * n + 1) * (6 * n + 2) * (6 * n + 3) *
  (6 * n + 4) * (6 * n + 5) * (6 * n + 6)

tripleStep : (n : Nat) → 3 * suc n ≡ suc (suc (suc (3 * n)))
tripleStep = solve 1
  (λ n → con 3 :* (con 1 :+ n) := con 3 :+ con 3 :* n) refl

sixStep : (n : Nat) →
  6 * suc n ≡ suc (suc (suc (suc (suc (suc (6 * n))))))
sixStep = solve 1
  (λ n → con 6 :* (con 1 :+ n) := con 6 :+ con 6 :* n) refl

factThreeStep : (n : Nat) → (3 * suc n) ! ≡ block3 n * (3 * n) !
factThreeStep n rewrite tripleStep n =
  solve 2 (λ x f →
    (con 3 :+ x) :* ((con 2 :+ x) :* ((con 1 :+ x) :* f))
    := ((x :+ con 1) :* (x :+ con 2) :* (x :+ con 3)) :* f)
    refl (3 * n) ((3 * n) !)

factSixStep : (n : Nat) → (6 * suc n) ! ≡ block6 n * (6 * n) !
factSixStep n rewrite sixStep n =
  solve 2 (λ x f →
    (con 6 :+ x) :* ((con 5 :+ x) :* ((con 4 :+ x) :*
      ((con 3 :+ x) :* ((con 2 :+ x) :* ((con 1 :+ x) :* f)))))
    := ((x :+ con 1) :* (x :+ con 2) :* (x :+ con 3) :*
        (x :+ con 4) :* (x :+ con 5) :* (x :+ con 6)) :* f)
    refl (6 * n) ((6 * n) !)

-- All six new factorial factors split into the three retained
-- denominator factors and the literal original leaf magnitude.
leafBlock : (n : Nat) → G.leafMagnitude n * block3 n ≡ block6 n
leafBlock = solve 1
  (λ n →
    (con 24 :* (con 2 :* n :+ con 1) :*
      (con 6 :* n :+ con 1) :* (con 6 :* n :+ con 5))
    :* ((con 3 :* n :+ con 1) :* (con 3 :* n :+ con 2) :*
      (con 3 :* n :+ con 3))
    :=
    (con 6 :* n :+ con 1) :* (con 6 :* n :+ con 2) :*
    (con 6 :* n :+ con 3) :* (con 6 :* n :+ con 4) :*
    (con 6 :* n :+ con 5) :* (con 6 :* n :+ con 6)) refl

sign : Nat → Z.ℤ
sign zero = Z.+_ 1
sign (suc n) = Z._*_ (Z.-_ (Z.+_ 1)) (sign n)

signedNumerator : Nat → Z.ℤ
signedNumerator n = Z._*_ (sign n) (Z.+_ ((6 * n) !))

-- P_(n+1) contains the n=0 unit leaf. The sign is the actual
-- signed product; there is no absolute-value replacement.
pFactorial : (n : Nat) →
  Z._*_ (E.P (suc n)) (Z.+_ ((3 * n) !)) ≡ signedNumerator n
pFactorial zero = refl
pFactorial (suc n)
  rewrite E.prefixPStep (suc n) | G.sourcePNegativeMagnitude n
        | factThreeStep n | factSixStep n
        | sym (I.-1*i≡-i (Z.+_ (G.leafMagnitude n))) =
  trans
    (zs 4
      (λ p a b c →
        (p ⊗ (zk (Z.-_ (Z.+_ 1)) ⊗ a)) ⊗ (b ⊗ c)
          ⊜ zk (Z.-_ (Z.+_ 1)) ⊗ (p ⊗ c) ⊗ (a ⊗ b))
      refl (E.P (suc n)) (Z.+_ (G.leafMagnitude n))
        (Z.+_ (block3 n)) (Z.+_ ((3 * n) !)))
    (trans
      (trans
        (cong (λ b → Z._*_ (Z._*_ (Z.-_ (Z.+_ 1))
              (Z._*_ (E.P (suc n)) (Z.+_ ((3 * n) !)))) (Z.+_ b))
          (leafBlock n))
        (cong (λ z → Z._*_ (Z._*_ (Z.-_ (Z.+_ 1)) z)
                      (Z.+_ (block6 n))) (pFactorial n)))
      (zs 3 (λ s f b →
        (zk (Z.-_ (Z.+_ 1)) ⊗ (s ⊗ f)) ⊗ b
          ⊜ (zk (Z.-_ (Z.+_ 1)) ⊗ s) ⊗ (b ⊗ f))
        refl (sign n) (Z.+_ ((6 * n) !)) (Z.+_ (block6 n))))

factorialDenBase : Nat → Nat
factorialDenBase n = CH.C ^ n * ((n !) ^ 3)

factorialDenStep : (n : Nat) →
  factorialDenBase (suc n) ≡ factorialDenBase n * G.qNat (suc n)
factorialDenStep n =
  solve 4 (λ c p k f →
    (c :* p) :* ((k :* f) :* ((k :* f) :* ((k :* f) :* con 1)))
    := (p :* (f :* (f :* (f :* con 1)))) :*
      (c :* (k :* (k :* (k :* con 1)))))
    refl CH.C (CH.C ^ n) (suc n) (n !)

qFactorial : (n : Nat) → G.qProduct (suc n) ≡ factorialDenBase n
qFactorial zero = refl
qFactorial (suc n) rewrite qFactorial n = sym (factorialDenStep n)

-- These equalities pin the actual raw fields to the classical
-- factorial fraction. We retain the unreduced raw state for consumers.
fullDenominator : Nat → Nat
fullDenominator n = factorialDenBase n * ((3 * n) !)

fullDenNonZero : (n : Nat) → N.NonZero (fullDenominator n)
fullDenNonZero n = NP.m*n≢0 (factorialDenBase n) ((3 * n) !)
  {{NP.m*n≢0 (CH.C ^ n) ((n !) ^ 3)
    {{NP.m^n≢0 CH.C n}} {{NP.m^n≢0 (n !) 3 {{NP._!≢0 n}}}}}}
  {{NP._!≢0 (3 * n)}}

factorialTerm : Nat → Q.ℚᵘ
factorialTerm n = P.frac (signedNumerator n) (fullDenominator n) (fullDenNonZero n)

-- General scaling by a nonzero natural in the SAME unnormalised
-- rational carrier. No normalization to gcd or alternative real.
scaleFrac : (a : Z.ℤ) (d e : Nat) (hd : N.NonZero d) (he : N.NonZero e) →
  P.frac a d hd Q.≃
  P.frac (Z._*_ a (Z.+_ e)) (d * e) (P.prodNZ d e hd he)
scaleFrac a zero e hd he =
  ⊥-elim (N.≢-nonZero⁻¹ zero {{hd}} refl)
scaleFrac a (suc d) zero hd he =
  ⊥-elim (N.≢-nonZero⁻¹ zero {{he}} refl)
scaleFrac a (suc d) (suc e) hd he =
  Q.*≡* (zs 3 (λ a d e → a ⊗ (d ⊗ e) ⊜ (a ⊗ e) ⊗ d)
    refl a (Z.+_ (suc d)) (Z.+_ (suc e)))

productFactorial : (n : Nat) → P.rawProduct (suc n) Q.≃ factorialTerm n
productFactorial n = QP.≃-trans
  (scaleFrac (E.P (suc n)) (G.qProduct (suc n)) ((3 * n) !)
    (G.qProductNonZero (suc n)) (NP._!≢0 (3 * n)))
  scaled
  where
  scaled : P.frac (Z._*_ (E.P (suc n)) (Z.+_ ((3 * n) !)))
    (G.qProduct (suc n) * ((3 * n) !))
    (P.prodNZ (G.qProduct (suc n)) ((3 * n) !)
      (G.qProductNonZero (suc n)) (NP._!≢0 (3 * n)))
    Q.≃ factorialTerm n
  scaled rewrite pFactorial n | qFactorial n = QP.≃-refl

factorialPrefix : Nat → Q.ℚᵘ
factorialPrefix zero = Q.0ℚᵘ
factorialPrefix (suc n) = factorialPrefix n Q.+ (factorialTerm n Q.* P.weight n)

sumFactorial : (n : Nat) → P.rawSum n Q.≃ factorialPrefix n
sumFactorial zero = QP.≃-refl
sumFactorial (suc n) = QP.≃-trans (P.rawSumStep n)
  (QP.+-cong (sumFactorial n)
    (QP.*-cong (productFactorial n) QP.≃-refl))
