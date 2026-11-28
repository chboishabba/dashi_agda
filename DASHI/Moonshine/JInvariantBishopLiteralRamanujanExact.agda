module DASHI.Moonshine.JInvariantBishopLiteralRamanujanExact where

-- Source-written, uncompiled. The three literal all-index Ramanujan
-- equations, on the existing E2/E4/E6 Bishop Cauchy ring. The finite
-- divisor geometry owns all positive coefficients; zero is explicit.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (ℤ; +_)
import Data.Integer.Base as Z
open import Data.Rational.Unnormalised using (_/_)
import Data.Rational.Unnormalised as Q
open import Relation.Binary.PropositionalEquality using (cong)
import Real as R
open R using (ℝ; _≃_; _+_; _*_; _-_; _⋆)
import RealProperties as P
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Foundations.BishopFiniteCauchyRingWeldExact as Ring
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionIntegerRowExact as I
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionRamanujanIntegerExact as A
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionSigmaFoldExact as V
import DASHI.Mathematics.NumberTheory.FiniteFactorPairPowerReadoutExact as Read
import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumExact as Pow
import DASHI.Mathematics.NumberTheory.FiniteDivisorSumExact as Div
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopHyperQDefectReductionExact as T
import DASHI.Moonshine.JInvariantBishopHyperQFactorizationWeldExact as F
open U using (Series; X; Y; D; scale; _⊗s_; _⊖s_)
open T using (E)
open I using (embed; embedAdd; embedMul; embedCong)

-- Reflect polynomial identities without trusting a foreign Bool.
data Expr : Set where
  lit : ℤ → Expr
  add mul : Expr → Expr → Expr

int : Expr → ℤ
int (lit z) = z
int (add a b) = Z._+_ (int a) (int b)
int (mul a b) = Z._*_ (int a) (int b)

real : Expr → ℝ
real (lit z) = embed z
real (add a b) = real a + real b
real (mul a b) = real a * real b

reflect : (e : Expr) → embed (int e) ≃ real e
reflect (lit z) = P.≃-refl
reflect (add a b) = P.≃-trans (embedAdd (int a) (int b)) (P.+-cong (reflect a) (reflect b))
reflect (mul a b) = P.≃-trans (embedMul (int a) (int b)) (P.*-cong (reflect a) (reflect b))

open import Agda.Builtin.Equality using (_≡_)

reflectEq : (a b : Expr) → int a ≡ int b → real a ≃ real b
reflectEq a b h = P.≃-trans (P.≃-symm (reflect a))
  (P.≃-trans (embedCong h) (reflect b))

infixl 6 _⊕e_
infixl 7 _⊗e_
_⊕e_ _⊗e_ : Expr → Expr → Expr
_⊕e_ = add
_⊗e_ = mul

neg : Nat → ℤ
neg n = Z.- (+ n)
c : Nat → Expr
c n = lit (+ n)
nc : Nat → Expr
nc n = lit (neg n)
s : Nat → Nat → Expr
s k n = lit (V.sigma k n)
v : Nat → Nat → Nat → Expr
v k l n = lit (V.conv k l n)

sigmaR : Nat → Nat → ℝ
sigmaR k n = real (s k n)
convR : Nat → Nat → Nat → ℝ
convR k l n = real (v k l n)

mExpr : Nat → Expr
mExpr n = c (suc n)

r11 : (n : Nat) → real (c 12 ⊗e v 1 1 (suc n)) ≃
  real (c 5 ⊗e s 3 (suc n) ⊕e (c 1 ⊕e nc 6 ⊗e mExpr n) ⊗e s 1 (suc n))
r11 n = reflectEq _ _ (A.c11 n)

r13 : (n : Nat) → real (c 240 ⊗e v 1 3 (suc n)) ≃
  real (c 21 ⊗e s 5 (suc n) ⊕e (c 10 ⊕e nc 30 ⊗e mExpr n) ⊗e s 3 (suc n) ⊕e nc 1 ⊗e s 1 (suc n))
r13 n = reflectEq _ _ (A.c13 n)

r15 : (n : Nat) → real (c 5040 ⊗e v 1 5 (suc n) ⊕e nc 24000 ⊗e v 3 3 (suc n)) ≃
  real ((c 210 ⊕e nc 420 ⊗e mExpr n) ⊗e s 5 (suc n) ⊕e c 10 ⊗e s 1 (suc n) ⊕e c 200 ⊗e s 3 (suc n))
r15 n = reflectEq _ _ (A.c15Scaled n)

actualE : (n : Nat) → embed (I.coefficient 1 (neg 24) n) ≃ E n
actualE zero = P.≃-refl
actualE (suc n) =
  P.≃-trans (embedMul (neg 24) (V.sigma 1 (suc n)))
    (P.≃-trans (P.*-congˡ (embedCong (cong +_ (Read.sigmaPowerOne (suc n)))))
      (P.≃-trans
        (let open P.ℝ-Solver in solve 1 (λ x → Κ (neg 24 / 1) ⊗ x ⊜ ⊝ (Κ (+ 24 / 1) ⊗ x))
          P.≃-refl (NR.natReal (Div.sigma1 (suc n))))
        (P.-‿cong (P.≃-symm (NR.natRealMul 24 (Div.sigma1 (suc n)))))))

actualX : (n : Nat) → embed (I.coefficient 3 (+ 240) n) ≃ X n
actualX zero = P.≃-refl
actualX (suc n) = P.≃-trans (embedMul (+ 240) (V.sigma 3 (suc n)))
  (P.≃-symm (NR.natRealMul 240 (Pow.sigmaPower 3 (suc n))))

actualY : (n : Nat) → embed (I.coefficient 5 (neg 504) n) ≃ Y n
actualY zero = P.≃-refl
actualY (suc n) = P.≃-trans (embedMul (neg 504) (V.sigma 5 (suc n)))
  (P.≃-trans (let open P.ℝ-Solver in solve 1
    (λ x → Κ (neg 504 / 1) ⊗ x ⊜ ⊝ (Κ (+ 504 / 1) ⊗ x))
    P.≃-refl (sigmaR 5 (suc n)))
    (P.-‿cong (P.≃-symm (NR.natRealMul 504 (Pow.sigmaPower 5 (suc n))))))

rowRead : (k l : Nat) (a b : ℤ) (f g : Series) →
  (∀ n → embed (I.coefficient k a n) ≃ f n) →
  (∀ n → embed (I.coefficient l b n) ≃ g n) →
  (n : Nat) → (f ⊗s g) (suc n) ≃
    real (lit a ⊗e s k (suc n) ⊕e lit b ⊗e s l (suc n) ⊕e
      (lit a ⊗e lit b) ⊗e v k l (suc n))
rowRead k l a b f g hf hg n =
  P.≃-trans (Ring.rowCong f g (λ i → embed (I.coefficient k a i)) (λ i → embed (I.coefficient l b i))
    (λ i → P.≃-symm (hf i)) (λ i → P.≃-symm (hg i)) (suc n))
    (P.≃-trans (P.≃-symm (I.rowEmbed (I.coefficient k a) (I.coefficient l b) (suc n)))
      (P.≃-trans (embedCong (I.rowPositive k l a b n))
        (reflect (lit a ⊗e s k (suc n) ⊕e lit b ⊗e s l (suc n) ⊕e (lit a ⊗e lit b) ⊗e v k l (suc n)))))

ee = rowRead 1 1 (neg 24) (neg 24) E E actualE actualE
ex = rowRead 1 3 (neg 24) (+ 240) E X actualE actualX
ey = rowRead 1 5 (neg 24) (neg 504) E Y actualE actualY
xx = rowRead 3 3 (+ 240) (+ 240) X X actualX actualX

ep : (n : Nat) → E (suc n) ≃ embed (neg 24) * sigmaR 1 (suc n)
ep n = P.≃-trans (P.≃-symm (actualE (suc n))) (embedMul (neg 24) (V.sigma 1 (suc n)))
xp : (n : Nat) → X (suc n) ≃ embed (+ 240) * sigmaR 3 (suc n)
xp n = P.≃-trans (P.≃-symm (actualX (suc n))) (embedMul (+ 240) (V.sigma 3 (suc n)))
yp : (n : Nat) → Y (suc n) ≃ embed (neg 504) * sigmaR 5 (suc n)
yp n = P.≃-trans (P.≃-symm (actualY (suc n))) (embedMul (neg 504) (V.sigma 5 (suc n)))

dPositive : (f : Series) (n : Nat) → D 1 f (suc n) ≃ NR.natReal (suc n) * f (suc n)
dPositive f n = P.*-congʳ (P.*-identityˡ (NR.natReal (suc n)))

unitRow : (f g : Series) → f zero ≃ R.1ℝ → g zero ≃ R.1ℝ →
  (f ⊗s g) zero ≃ R.1ℝ
unitRow f g hf hg = P.≃-trans (U.mul0 {f = f} {g = g} hf hg) U.unitMul

zeroRhs : (a b : Series) (q : ℝ) → a zero ≃ R.1ℝ → b zero ≃ R.1ℝ →
  scale q (a ⊖s b) zero ≃ R.0ℝ
zeroRhs a b q ha hb = U.right0
  (P.≃-trans (P.+-cong ha (P.-‿cong hb)) (P.+-inverseʳ R.1ℝ))

ramanujanE : F.RamanujanE
ramanujanE zero = P.≃-trans (U.D0 E)
  (P.≃-symm (zeroRhs (E ⊗s E) X ((+ 1 / 12) ⋆)
    (unitRow E E P.≃-refl P.≃-refl) P.≃-refl))
ramanujanE (suc n) =
  let a = sigmaR 1 (suc n)
      b = sigmaR 3 (suc n)
      t = convR 1 1 (suc n)
      m = NR.natReal (suc n)
      open P.ℝ-Solver
      h = P.≃-trans (P.*-congˡ (P.+-cong (ee n) (P.-‿cong (xp n))))
        (P.≃-trans (solve 3 (λ a b t →
          Κ (+ 1 / 12) ⊗ (Κ (neg 24 / 1) ⊗ a ⊕ Κ (neg 24 / 1) ⊗ a ⊕
            (Κ (neg 24 / 1) ⊗ Κ (neg 24 / 1)) ⊗ t ⊖ Κ (+ 240 / 1) ⊗ b)
          ⊜ Κ (+ 4 / 1) ⊗ (Κ (+ 12 / 1) ⊗ t) ⊖ Κ (+ 4 / 1) ⊗ a ⊖ Κ (+ 20 / 1) ⊗ b)
          P.≃-refl a b t)
          (P.≃-trans (P.+-cong (P.+-cong (P.*-congˡ (r11 n)) P.≃-refl) P.≃-refl)
            (solve 3 (λ a b m → Κ (+ 4 / 1) ⊗ (Κ (+ 5 / 1) ⊗ b ⊕
              (Κ (+ 1 / 1) ⊕ Κ (neg 6 / 1) ⊗ m) ⊗ a) ⊖ Κ (+ 4 / 1) ⊗ a ⊖ Κ (+ 20 / 1) ⊗ b
              ⊜ m ⊗ (Κ (neg 24 / 1) ⊗ a)) P.≃-refl a b m)))
  in P.≃-trans (dPositive E n) (P.≃-trans (P.*-congˡ (ep n)) (P.≃-symm h))

ramanujanX : F.RamanujanX
ramanujanX zero = P.≃-trans (U.D0 X)
  (P.≃-symm (zeroRhs (E ⊗s X) Y ((+ 1 / 3) ⋆)
    (unitRow E X P.≃-refl P.≃-refl) P.≃-refl))
ramanujanX (suc n) =
  let a = sigmaR 1 (suc n)
      b = sigmaR 3 (suc n)
      d = sigmaR 5 (suc n)
      t = convR 1 3 (suc n)
      m = NR.natReal (suc n)
      open P.ℝ-Solver
      h = P.≃-trans (P.*-congˡ (P.+-cong (ex n) (P.-‿cong (yp n))))
        (P.≃-trans (solve 4 (λ a b d t →
          Κ (+ 1 / 3) ⊗ (Κ (neg 24 / 1) ⊗ a ⊕ Κ (+ 240 / 1) ⊗ b ⊕
            (Κ (neg 24 / 1) ⊗ Κ (+ 240 / 1)) ⊗ t ⊖ Κ (neg 504 / 1) ⊗ d)
          ⊜ Κ (neg 8 / 1) ⊗ (Κ (+ 240 / 1) ⊗ t) ⊕
            (Κ (+ 80 / 1) ⊗ b ⊖ Κ (+ 8 / 1) ⊗ a ⊕ Κ (+ 168 / 1) ⊗ d))
          P.≃-refl a b d t)
          (P.≃-trans (P.+-cong (P.*-congˡ (r13 n)) P.≃-refl)
            (solve 4 (λ a b d m → Κ (neg 8 / 1) ⊗ (Κ (+ 21 / 1) ⊗ d ⊕
              (Κ (+ 10 / 1) ⊕ Κ (neg 30 / 1) ⊗ m) ⊗ b ⊕ Κ (neg 1 / 1) ⊗ a) ⊕
                (Κ (+ 80 / 1) ⊗ b ⊖ Κ (+ 8 / 1) ⊗ a ⊕ Κ (+ 168 / 1) ⊗ d)
              ⊜ m ⊗ (Κ (+ 240 / 1) ⊗ b)) P.≃-refl a b d m)))
  in P.≃-trans (dPositive X n) (P.≃-trans (P.*-congˡ (xp n)) (P.≃-symm h))

ramanujanY : F.RamanujanY
ramanujanY zero = P.≃-trans (U.D0 Y)
  (P.≃-symm (zeroRhs (E ⊗s Y) (X ⊗s X) ((+ 1 / 2) ⋆)
    (unitRow E Y P.≃-refl P.≃-refl) (unitRow X X P.≃-refl P.≃-refl)))
ramanujanY (suc n) =
  let a = sigmaR 1 (suc n)
      b = sigmaR 3 (suc n)
      d = sigmaR 5 (suc n)
      t = convR 1 5 (suc n)
      u = convR 3 3 (suc n)
      m = NR.natReal (suc n)
      open P.ℝ-Solver
      h = P.≃-trans (P.*-congˡ (P.+-cong (ey n) (P.-‿cong (xx n))))
        (P.≃-trans (solve 5 (λ a b d t u →
          Κ (+ 1 / 2) ⊗ (Κ (neg 24 / 1) ⊗ a ⊕ Κ (neg 504 / 1) ⊗ d ⊕
            (Κ (neg 24 / 1) ⊗ Κ (neg 504 / 1)) ⊗ t ⊖
              (Κ (+ 240 / 1) ⊗ b ⊕ Κ (+ 240 / 1) ⊗ b ⊕ (Κ (+ 240 / 1) ⊗ Κ (+ 240 / 1)) ⊗ u))
          ⊜ Κ (+ 6 / 5) ⊗ (Κ (+ 5040 / 1) ⊗ t ⊕ Κ (neg 24000 / 1) ⊗ u) ⊕
            (Κ (neg 12 / 1) ⊗ a ⊖ Κ (+ 252 / 1) ⊗ d ⊖ Κ (+ 240 / 1) ⊗ b))
          P.≃-refl a b d t u)
          (P.≃-trans (P.+-cong (P.*-congˡ (r15 n)) P.≃-refl)
            (solve 4 (λ a b d m → Κ (+ 6 / 5) ⊗
              ((Κ (+ 210 / 1) ⊕ Κ (neg 420 / 1) ⊗ m) ⊗ d ⊕ Κ (+ 10 / 1) ⊗ a ⊕ Κ (+ 200 / 1) ⊗ b)
                ⊕ (Κ (neg 12 / 1) ⊗ a ⊖ Κ (+ 252 / 1) ⊗ d ⊖ Κ (+ 240 / 1) ⊗ b)
              ⊜ m ⊗ (Κ (neg 504 / 1) ⊗ d)) P.≃-refl a b d m)))
  in P.≃-trans (dPositive Y n) (P.≃-trans (P.*-congˡ (yp n)) (P.≃-symm h))
